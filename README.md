# sys4lang

This repository contains a collection of tools for AliceSoft's System 4 game engine. It integrates a compiler (`sys4c`), a decompiler (`sys4dc`), and a language server (`sys4lsp`).

Games up to Heartful Maman (early 2017) are currently supported. Games from Beat Valkyrie Ixseal onwards are not yet supported.

## Components

*   **sys4c (Compiler):** A compiler for System 4. This is primarily intended for building source files that were decompiled using `sys4dc`. Unlike AinDecompiler, it focuses on full builds and cannot modify only specific functions in an existing `.ain` file.

*   **sys4dc (Decompiler):** A decompiler for System 4 `.ain` files.

*   **sys4lsp (Language Server):** A language server for the System 4 programming language.

## Installation

Pre-built binaries for Windows (x64) and Linux (x64) are available on the [GitHub releases page](https://github.com/kichikuou/sys4lang/releases).

### Building from Source

To build and install the tools from source, you need to have OCaml and opam installed. Then, run the following commands:

```sh
$ git clone https://github.com/kichikuou/sys4lang.git
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

## Command Reference

### sys4c

`sys4c` is the System 4 compiler. It has two subcommands.

#### `sys4c build PROJECT`

Build a System 4 project from a `.pje` project file. This is the typical way to compile a decompiled game.

```sh
$ sys4c build src/SengokuRance.pje
```

Options:

| Option | Description |
|--------|-------------|
| `--output-dir OUTPUT_DIR` | Override the output directory specified in the `.pje` file. |

#### `sys4c compile SOURCES...`

Compile one or more `.jaf` source files (and optionally `.hll` library files) directly, without a project file.

```sh
$ sys4c compile -o out.ain foo.jaf bar.jaf
```

Options:

| Option | Default | Description |
|--------|---------|-------------|
| `-o, --output OUT_FILE` | `out.ain` | Output `.ain` file path. |
| `--ain-version MAJOR` | `4` | Major version of the output `.ain` file. |
| `--ain-minor-version MINOR` | `0` | Minor version of the output `.ain` file. |
| `--import-as HLL_NAME=NAME` | | Import an `.hll` file under a different name. Can be specified multiple times. |
| `--input-encoding ENCODING` | `UTF-8` | Input file encoding: `UTF-8` or `Shift_JIS`. |

### sys4dc

`sys4dc` decompiles a `.ain` file into JAF source files.

```sh
$ sys4dc -o src SengokuRance.ain
```

Arguments:

| Argument | Description |
|----------|-------------|
| `AIN_FILE` | The `.ain` file to decompile. |

Options:

| Option | Description |
|--------|-------------|
| `-o DIRECTORY` | Output directory. Use `-` to print all output to stdout. Defaults to the current directory. |
| `--address` | Print bytecode addresses as comments in the output. |
| `--inspect FUNCTION` | Print detailed information about the decompilation process for a single function, instead of decompiling the entire file. |
| `--move-to-original-file` | Move overridden functions to the files where they were originally defined. Useful for mods created with AinDecompiler. |
| `--continue-on-error` | Continue decompilation even if an error is encountered in one function. |

### sys4lsp

`sys4lsp` is a Language Server Protocol server for the System 4 language. It is normally launched automatically by an LSP client (such as a VS Code extension) and communicates over stdio.

```sh
$ sys4lsp [PJE_FILE]
```

The optional `PJE_FILE` argument specifies the `.pje` project file to load. It is used as a fallback when the LSP client does not provide a `pjePath` via the `initializationOptions` of the `initialize` request.

**Initialization Options**

The LSP client may pass the following fields in the `initializationOptions` object of the `initialize` request:

| Field | Description |
|-------|-------------|
| `pjePath` | Path to the `.pje` project file to load. Takes precedence over the command-line argument. |

## Credits

The `sys4c` compiler and `sys4lsp` language server are derived from the original [sys4c compiler](https://github.com/nunuhara/sys4c) by [@nunuhara](https://github.com/nunuhara).
