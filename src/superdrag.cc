#include "superdrag.h"

#include <windows.h>

#include <objidl.h>
#include <shlobj.h>

#include <algorithm>
#include <array>
#include <cctype>
#include <cstdint>
#include <optional>
#include <ranges>
#include <string>
#include <string_view>

#include "config.h"
#include "detours.h"
#include "inputhook.h"
#include "utils.h"

namespace {

constexpr uint32_t kSharedMagic = 0x53444731;  // "SDG1"
constexpr size_t kMaxUrlChars = 4096;
constexpr ULONGLONG kRecordTimeoutMs = 5000;

struct SharedDragRecord {
  volatile LONG ready;
  uint32_t magic;
  uint64_t captured_ticks;
  wchar_t url[kMaxUrlChars];
};

HANDLE drag_mapping = nullptr;
SharedDragRecord* drag_record = nullptr;
POINT lbutton_down_point = {-1, -1};

using DoDragDropFn = HRESULT(WINAPI*)(IDataObject*, IDropSource*, DWORD,
                                      DWORD*);
DoDragDropFn original_do_drag_drop = nullptr;

std::wstring GetMappingName(DWORD browser_pid) {
  return L"Local\\ChromePlusSuperDrag-" + std::to_wstring(browser_pid);
}

bool IsValidUrl(std::wstring_view url) {
  if (url.empty() || url.size() >= kMaxUrlChars) {
    return false;
  }
  return !url.starts_with(L"javascript:");
}

std::optional<std::string> GetHGlobalText(IDataObject* data_object,
                                          CLIPFORMAT format) {
  if (!data_object) {
    return std::nullopt;
  }

  FORMATETC format_etc = {format, nullptr, DVASPECT_CONTENT, -1,
                           TYMED_HGLOBAL};
  STGMEDIUM medium = {};
  if (FAILED(data_object->GetData(&format_etc, &medium)) ||
      medium.tymed != TYMED_HGLOBAL || !medium.hGlobal) {
    return std::nullopt;
  }

  const void* locked = GlobalLock(medium.hGlobal);
  const SIZE_T bytes = GlobalSize(medium.hGlobal);
  std::optional<std::string> text;
  if (locked && bytes > 0) {
    const auto* first = static_cast<const char*>(locked);
    const auto* end = first + bytes;
    if (const auto* terminator = std::find(first, end, '\0');
        terminator != end) {
      text.emplace(first, terminator);
    }
  }
  if (locked) {
    GlobalUnlock(medium.hGlobal);
  }
  ReleaseStgMedium(&medium);
  return text;
}

std::optional<std::wstring> GetHGlobalWideText(IDataObject* data_object,
                                                CLIPFORMAT format) {
  if (!data_object) {
    return std::nullopt;
  }

  FORMATETC format_etc = {format, nullptr, DVASPECT_CONTENT, -1,
                           TYMED_HGLOBAL};
  STGMEDIUM medium = {};
  if (FAILED(data_object->GetData(&format_etc, &medium)) ||
      medium.tymed != TYMED_HGLOBAL || !medium.hGlobal) {
    return std::nullopt;
  }

  const auto* locked = static_cast<const wchar_t*>(GlobalLock(medium.hGlobal));
  const SIZE_T bytes = GlobalSize(medium.hGlobal);
  std::optional<std::wstring> text;
  if (locked && bytes >= sizeof(wchar_t)) {
    const size_t capacity = bytes / sizeof(wchar_t);
    const auto* end = locked + capacity;
    if (const auto* terminator = std::find(locked, end, L'\0');
        terminator != end) {
      text.emplace(locked, terminator);
    }
  }
  if (locked) {
    GlobalUnlock(medium.hGlobal);
  }
  ReleaseStgMedium(&medium);
  return text;
}

std::optional<std::string_view> GetHtmlFragment(std::string_view html) {
  const size_t header_end = html.find("\r\n\r\n");
  if (header_end == std::string_view::npos) {
    return std::nullopt;
  }

  const auto read_offset = [&](std::string_view name) -> std::optional<size_t> {
    const size_t name_pos = html.find(name);
    if (name_pos == std::string_view::npos || name_pos >= header_end) {
      return std::nullopt;
    }
    size_t value = 0;
    bool has_digit = false;
    for (size_t i = name_pos + name.size(); i < header_end; ++i) {
      const unsigned char ch = static_cast<unsigned char>(html[i]);
      if (ch == '\r' || ch == '\n') {
        break;
      }
      if (!std::isdigit(ch)) {
        continue;
      }
      has_digit = true;
      value = value * 10 + (ch - '0');
      if (value > html.size()) {
        return std::nullopt;
      }
    }
    return has_digit ? std::optional<size_t>(value) : std::nullopt;
  };

  const auto start = read_offset("StartFragment:");
  const auto end = read_offset("EndFragment:");
  if (!start || !end || *start >= *end || *end > html.size()) {
    return std::nullopt;
  }
  return html.substr(*start, *end - *start);
}

bool IsAsciiEqualIgnoreCase(char left, char right) {
  return std::tolower(static_cast<unsigned char>(left)) ==
         std::tolower(static_cast<unsigned char>(right));
}

bool StartsWithAsciiIgnoreCase(std::string_view text, std::string_view prefix) {
  return text.size() >= prefix.size() &&
         std::ranges::equal(text.substr(0, prefix.size()), prefix,
                            IsAsciiEqualIgnoreCase);
}

bool ContainsAsciiIgnoreCase(std::string_view text, std::string_view needle) {
  if (needle.empty() || needle.size() > text.size()) {
    return false;
  }
  for (size_t i = 0; i <= text.size() - needle.size(); ++i) {
    if (StartsWithAsciiIgnoreCase(text.substr(i), needle)) {
      return true;
    }
  }
  return false;
}

// Chromium's CF_HTML fragment preserves a dragged anchor as its first element.
// Reject image drags even when an image is wrapped by an anchor so native image
// dragging is left entirely to Chrome.
bool IsAnchorOnlyHtmlFragment(std::string_view fragment) {
  size_t pos = 0;
  while (pos < fragment.size()) {
    const size_t tag_start = fragment.find('<', pos);
    if (tag_start == std::string_view::npos) {
      return false;
    }
    if (fragment.substr(tag_start).starts_with("<!--")) {
      const size_t comment_end = fragment.find("-->", tag_start + 4);
      if (comment_end == std::string_view::npos) {
        return false;
      }
      pos = comment_end + 3;
      continue;
    }
    const size_t name_start = tag_start + 1;
    if (name_start >= fragment.size() || fragment[name_start] == '/') {
      return false;
    }
    const size_t tag_end = fragment.find('>', name_start);
    if (tag_end == std::string_view::npos) {
      return false;
    }
    const std::string_view tag = fragment.substr(name_start, tag_end - name_start);
    if (!StartsWithAsciiIgnoreCase(tag, "a") ||
        (tag.size() > 1 && !std::isspace(static_cast<unsigned char>(tag[1])) &&
         tag[1] != '/')) {
      return false;
    }
    if (!ContainsAsciiIgnoreCase(tag, "href")) {
      return false;
    }
    return !ContainsAsciiIgnoreCase(fragment.substr(tag_end + 1), "<img");
  }
  return false;
}

std::optional<std::wstring> GetDraggedAnchorUrl(IDataObject* data_object) {
  const CLIPFORMAT html_format = RegisterClipboardFormatW(L"HTML Format");
  const auto html = GetHGlobalText(data_object, html_format);
  if (!html) {
    return std::nullopt;
  }
  const auto fragment = GetHtmlFragment(*html);
  if (!fragment || !IsAnchorOnlyHtmlFragment(*fragment)) {
    return std::nullopt;
  }

  const CLIPFORMAT url_format = RegisterClipboardFormatW(CFSTR_INETURLW);
  const auto url = GetHGlobalWideText(data_object, url_format);
  return url && IsValidUrl(*url) ? url : std::nullopt;
}

void PublishDraggedUrl(std::wstring_view url) {
  HWND root = GetForegroundWindow();
  root = root ? GetAncestor(root, GA_ROOT) : nullptr;
  DWORD browser_pid = 0;
  if (!root || !IsChromeWindow(root) ||
      !GetWindowThreadProcessId(root, &browser_pid)) {
    return;
  }

  HANDLE mapping = OpenFileMappingW(FILE_MAP_WRITE, FALSE,
                                    GetMappingName(browser_pid).c_str());
  if (!mapping) {
    return;
  }
  auto* record = static_cast<SharedDragRecord*>(
      MapViewOfFile(mapping, FILE_MAP_WRITE, 0, 0, sizeof(SharedDragRecord)));
  if (!record) {
    CloseHandle(mapping);
    return;
  }

  InterlockedExchange(&record->ready, 0);
  record->magic = kSharedMagic;
  record->captured_ticks = GetTickCount64();
  std::copy(url.begin(), url.end(), record->url);
  record->url[url.size()] = L'\0';
  MemoryBarrier();
  InterlockedExchange(&record->ready, 1);
  UnmapViewOfFile(record);
  CloseHandle(mapping);
}

HRESULT WINAPI DetouredDoDragDrop(IDataObject* data_object,
                                  IDropSource* drop_source,
                                  DWORD ok_effects,
                                  DWORD* effect) {
  if (config.IsSuperDragOpenLink()) {
    if (const auto url = GetDraggedAnchorUrl(data_object)) {
      PublishDraggedUrl(*url);
    }
  }
  return original_do_drag_drop(data_object, drop_source, ok_effects, effect);
}

void ClearRecord() {
  if (drag_record) {
    InterlockedExchange(&drag_record->ready, 0);
  }
}

std::optional<std::wstring> TakeRecentRecord() {
  if (!drag_record || InterlockedCompareExchange(&drag_record->ready, 0, 0) == 0) {
    return std::nullopt;
  }
  MemoryBarrier();
  if (drag_record->magic != kSharedMagic ||
      GetTickCount64() - drag_record->captured_ticks > kRecordTimeoutMs) {
    ClearRecord();
    return std::nullopt;
  }
  const std::wstring url(drag_record->url);
  ClearRecord();
  return IsValidUrl(url) ? std::optional<std::wstring>(url) : std::nullopt;
}

bool HasMovedFarEnough(POINT up_point) {
  if (lbutton_down_point.x < 0 || lbutton_down_point.y < 0) {
    return false;
  }
  const LONG dx = std::abs(up_point.x - lbutton_down_point.x);
  const LONG dy = std::abs(up_point.y - lbutton_down_point.y);
  const LONG distance = config.GetSuperDragDistance();
  return dx > distance || dy > distance;
}

bool SendModifiedClickAt(POINT point, bool background) {
  POINT cursor;
  if (!GetCursorPos(&cursor) || !SetCursorPos(point.x, point.y)) {
    return false;
  }

  const auto keyboard_input = [](WORD key, DWORD flags) {
    INPUT input = {};
    input.type = INPUT_KEYBOARD;
    input.ki.wVk = key;
    input.ki.dwFlags = flags;
    input.ki.dwExtraInfo = GetMagicCode();
    return input;
  };
  const auto mouse_input = [](DWORD flags) {
    INPUT input = {};
    input.type = INPUT_MOUSE;
    input.mi.dwFlags = flags;
    input.mi.dwExtraInfo = GetMagicCode();
    return input;
  };
  const std::array<INPUT, 6> inputs = {
      keyboard_input(VK_CONTROL, KEYEVENTF_EXTENDEDKEY),
      keyboard_input(VK_SHIFT, KEYEVENTF_EXTENDEDKEY),
      mouse_input(MOUSEEVENTF_LEFTDOWN),
      mouse_input(MOUSEEVENTF_LEFTUP),
      keyboard_input(VK_SHIFT, KEYEVENTF_EXTENDEDKEY | KEYEVENTF_KEYUP),
      keyboard_input(VK_CONTROL, KEYEVENTF_EXTENDEDKEY | KEYEVENTF_KEYUP),
  };
  // Ctrl-click is Chromium's native background-tab disposition; adding Shift
  // makes Chromium activate the new tab. Keep the event in Chrome's own link
  // activation path rather than depending on private browser ABI addresses.
  const UINT count = background ? 4 : static_cast<UINT>(inputs.size());
  std::array<INPUT, 4> background_inputs = {inputs[0], inputs[2], inputs[3],
                                             inputs[5]};
  const UINT sent = background
                        ? SendInput(count, background_inputs.data(), sizeof(INPUT))
                        : SendInput(count, inputs.data(), sizeof(INPUT));
  SetCursorPos(cursor.x, cursor.y);
  return sent == count;
}

bool SuperDragMouseHandler(WPARAM w_param, LPARAM l_param) {
  if (!config.IsSuperDragOpenLink()) {
    return false;
  }
  const auto* mouse = reinterpret_cast<const MOUSEHOOKSTRUCT*>(l_param);
  if (w_param == WM_LBUTTONDOWN) {
    lbutton_down_point = mouse->pt;
    ClearRecord();
    return false;
  }
  if (w_param != WM_LBUTTONUP || !HasMovedFarEnough(mouse->pt)) {
    return false;
  }
  const auto url = TakeRecentRecord();
  if (!url) {
    return false;
  }
  return SendModifiedClickAt(lbutton_down_point, config.IsSuperDragBackground());
}

}  // namespace

void InitializeSuperDragBrowser() {
  if (!config.IsSuperDragOpenLink()) {
    return;
  }
  drag_mapping = CreateFileMappingW(INVALID_HANDLE_VALUE, nullptr, PAGE_READWRITE,
                                    0, sizeof(SharedDragRecord),
                                    GetMappingName(GetCurrentProcessId()).c_str());
  if (!drag_mapping) {
    DebugLog(L"super drag: CreateFileMapping failed: {}", GetLastError());
    return;
  }
  drag_record = static_cast<SharedDragRecord*>(
      MapViewOfFile(drag_mapping, FILE_MAP_ALL_ACCESS, 0, 0,
                    sizeof(SharedDragRecord)));
  if (!drag_record) {
    DebugLog(L"super drag: MapViewOfFile failed: {}", GetLastError());
    CloseHandle(drag_mapping);
    drag_mapping = nullptr;
    return;
  }
  ZeroMemory(drag_record, sizeof(*drag_record));
  RegisterMouseHandler(SuperDragMouseHandler, HandlerPriority::kHigh);
}

void InitializeSuperDragRenderer() {
  if (!config.IsSuperDragOpenLink() || original_do_drag_drop) {
    return;
  }
  const HMODULE ole32 = GetModuleHandleW(L"ole32.dll");
  const auto do_drag_drop = ole32 ? reinterpret_cast<DoDragDropFn>(
                                    GetProcAddress(ole32, "DoDragDrop"))
                              : nullptr;
  if (!do_drag_drop) {
    DebugLog(L"super drag: DoDragDrop was not found");
    return;
  }

  original_do_drag_drop = do_drag_drop;
  DetourTransactionBegin();
  DetourUpdateThread(GetCurrentThread());
  DetourAttach(reinterpret_cast<PVOID*>(&original_do_drag_drop),
               DetouredDoDragDrop);
  const LONG status = DetourTransactionCommit();
  if (status != NO_ERROR) {
    DebugLog(L"super drag: DetourAttach(DoDragDrop) failed: {}", status);
    original_do_drag_drop = nullptr;
  }
}
