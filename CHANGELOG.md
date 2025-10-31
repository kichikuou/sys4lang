# Changelog

## 0.6.0 - 2025-11-01
- Decompiler: Changed the generated code style to be more compact
- Compiler: Added support for the optional argument of `float.String()`
- Compiler: Fixed code generation bugs

## 0.5.0 - 2025-10-25
- The syntax for adding a function to a delegate has changed: write `delegate += f` instead of `delegate.Add(f)`
- Compiler: Allow `ref X foo = bool ? ref X : ref X;` (#1)
- Decompiler: Fixed isses with Rance 6 (MangaGamer), Pascha C++, Pastel Chime 3, Rance 9, Evenicle, Rance 03
- LSP: Fixed "Type error: expected unknown_functype; ..." errors for functype arguments
- Bugfixes

## 0.4.0 - 2025-10-10
- Compiler: Respects `Encoding` field in `.pje`
- Decompiler: Outputs to current directory if `-o` is not specified
- Decompiler: Sets `OutputDir` of `.pje` to the directory of original ain file

## 0.3.0 - 2025-10-07
- Compiler: Added `--output-dir` option to override `OutputDir` in `.pje`
- Decompiler: Added `--move-to-original-file` flag which is useful for mods made with AinDecompiler
- Decompiler: Removes broken `tagBusho::getSp()` function in Sengoku Rance
- LSP: Added support for `system4/entrypoint` custom request
- LSP: Fixed crash when hovering on functypes
- Requires Ocaml >= 5.2 to build

## 0.2.0 - 2025-10-01
- Initial release
