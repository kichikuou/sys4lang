# sys4lang

This repository contains a collection of tools for AliceSoft's System 4 game engine. It integrates a compiler (`sys4c`), a decompiler (`sys4dc`), and a language server (`sys4lsp`).

Games up to Heartful Maman (early 2017) are currently supported. Games from Beat Valkyrie Ixseal onwards are not yet supported.

## Components

*   **sys4c (Compiler):** A compiler for System 4. This is primarily intended for building source files that were decompiled using `sys4dc`. It can also patch selected functions and declarations into an existing `.ain` file.

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

Alternatively, use `sys4c patch` to apply only selected changes to the original `.ain` file. See [docs/patch.md](docs/patch.md).

## Command Reference

### sys4c

`sys4c` is the System 4 compiler. It has three subcommands.

#### `sys4c build PROJECT`

Build a System 4 project from a `.pje` project file. This is the typical way to compile a decompiled game.

```sh
$ sys4c build src/SengokuRance.pje
```

Options:

| Option | Description |
|--------|-------------|
| `--output-dir OUTPUT_DIR` | Override the output directory specified in the `.pje` file. |
| `--no-debug-info` | Do not write the `debug_info.json` file. |

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

#### `sys4c patch PROJECT [TARGET...]`

Compile the selected functions and declarations of a project, and append them to an existing `.ain` file. See [docs/patch.md](docs/patch.md) for details.

```sh
$ sys4c patch src/SengokuRance.pje calculate_score --base-ain SengokuRance.ain -o SengokuRance-patched.ain
```

`TARGET` is the name of a function, method, constructor, destructor, structure, class, function type, or delegate type to apply.

Options:

| Option | Description |
|--------|-------------|
| `--base-ain FILE` | The `.ain` file to patch. Defaults to the `.ain` file of the project. |
| `-o, --output FILE` | Output `.ain` file path. Defaults to the `.ain` file of the project. |
| `--source FILE` | A patch source file. Its functions and types are applied, and its declarations replace the project declarations of the same names. Can be specified multiple times. |
| `--globals` | Add new globals and global groups, and rebuild the initialization of all globals. |
| `--keep-crc` | Keep the CRC values of the replaced functions. |
| `--debug-info` | Read and update the `debug_info.json` file. |

### sys4dc

`sys4dc` decompiles a `.ain` file into JAF source files.

```sh
$ sys4dc -o src SengokuRance.ain
```

Arguments:

| Argument | Description |
|----------|-------------|
| `AIN_FILE` | The `.ain` file to decompile. |
| `FUNCTION` | Optional. Restricts the output to a single function. With `--disassemble`/`--disassemble-raw`, only this function is disassembled; otherwise, detailed information about its decompilation process is printed. |

Options:

| Option | Description |
|--------|-------------|
| `-o DIRECTORY` | Output directory. Use `-` to print all output to stdout. Defaults to the current directory. |
| `--address` | Print bytecode addresses as comments in the output. |
| `--disassemble` | Disassemble the code section instead of decompiling. |
| `--disassemble-raw` | Like `--disassemble`, but without resolving identifiers or generating labels (raw listing with addresses). |
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
