#ifndef CHROME_PLUS_SRC_SUPERDRAG_H_
#define CHROME_PLUS_SRC_SUPERDRAG_H_

// Called in the browser process before InstallInputHooks().
void InitializeSuperDragBrowser();

// Called only in renderer processes. Captures Chromium's OLE link drag data.
void InitializeSuperDragRenderer();

#endif  // CHROME_PLUS_SRC_SUPERDRAG_H_
