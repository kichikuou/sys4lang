# Changelog

## 0.9.0 - 2026-06-06
- Compiler: **Scoping rule change for variable declarations in `for` loops.** A variable declared in the initializer of a `for` loop (e.g. `for (int i = 0; ...)`) is now placed in the enclosing scope, so it remains visible after the loop. Previously sys4c scoped the variable to the loop body (as C/Java do).
- Compiler, Decompiler: Added support for ain v0 (DALK gaiden) and v1 (Mamanyonyo).
- Compiler: Compilation speed improved by more than 3x for large projects such as Rance 9.
- Compiler: Fixed incorrect bytecode for `ref`-delegate operations.
- Decompiler: A variable declaration immediately before a `for` loop is now folded into the loop's initializer, e.g. `for (int i = 0; ...)` instead of `int i; for (i = 0; ...)`.

## 0.8.0 - 2026-04-29
- LSP: Added code completion for identifiers, member access (`.`), and built-in methods.
- LSP: Added function signature help -- when you type a function call, parameter names are shown and the current parameter is highlighted.
- LSP: Added find-all-references support.
- LSP: Fixed incorrect hover info for `Array` and `Delegate` built-in methods.
- Compiler: Fixed a code generation bug with `ref` parameters of scalar types in structs.
- Decompiler: Bugfixes.

## 0.7.2 - 2026-01-31
- Decompiler: Fixed an issue where floating-point numbers close to zero were output with lower precision than required.

## 0.7.1 - 2026-01-17
- LSP: Fixed an issue where project files failed to load on Windows.

## 0.7.0 - 2026-01-16
- Tsumamigui 3 and Heartful Maman are now supported.
- Compiler: `(type)expression` cast syntax has been removed. Please use `type(expression)` instead.
- Decompiler: Now `sys4dc` can produce output for Ixseal and Rance X (though they cannot be recompiled with `sys4c`).
- Decompiler: Added `--continue-on-error` command line flag.
- LSP: The language server no longer loads AIN file. Instead it scans all source files in the background.
- LSP: Added support for goto-definition for global constants and HLL functions.

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
