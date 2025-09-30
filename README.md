# sys4lang

This repository contains a collection of tools for AliceSoft's System 4 game engine. It integrates a compiler (`sys4c`), a decompiler (`sys4dc`), and a language server (`sys4lsp`).

Games released between 2003 (Daibanchou) and 2015 (Rance 03) are currently supported.

## Components

*   **sys4c (Compiler):** A compiler for System 4. This is primarily intended for building source files that were decompiled using `sys4dc`. Unlike AinDecompiler, it focuses on full builds and cannot modify only specific functions in an existing `.ain` file.

*   **sys4dc (Decompiler):** A decompiler for System 4 `.ain` files.

*   **sys4lsp (Language Server):** A language server for the System 4 programming language.

### Language Server Features

- [x] Diagnostics
- [x] Hover
- [x] Jump to Definition
- [ ] Find References
- [ ] Code Completion
- [ ] Signature Help
- [ ] Semantic Tokens

## Installation

To build and install the tools from source, you need to have OCaml and opam installed. Then, run the following commands:

```sh
$ git clone --recursive https://github.com/kichikuou/sys4lang.git
$ cd sys4lang
$ opam install . --deps-only --with-test
$ dune build
$ dune install
```

## Usage

The typical workflow is to decompile a game, edit the source code, and then recompile it.

### 1. Decompile

Use `sys4dc` to decompile an `.ain` file:

```sh
$ sys4dc -o src SengokuRance.ain
```

### 2. Edit

Edit the decompiled source code with editor support. If you're using Visual Studio Code, you can install the [System4 language extension](https://marketplace.visualstudio.com/items?itemName=kichikuou.system4) to get features like diagnostics, hover, and jump to definition. The language server (`sys4lsp`) is used automatically by the extension.

### 3. Compile

Use `sys4c` to build the source files:

```sh
$ sys4c build src/SengokuRance.pje
```

## Credits

The `sys4c` compiler and `sys4lsp` language server are derived from the original [sys4c compiler](https://github.com/nunuhara/sys4c) by [@nunuhara](https://github.com/nunuhara).
