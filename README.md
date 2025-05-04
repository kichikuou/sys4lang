# sys4c

This is a fork of [nunuhara/sys4c](https://github.com/nunuhara/sys4c).

Currently, it focuses on full builds. Unlike nunuhara/sys4c or AinDecompiler,
it cannot modify only specific functions in an existing `.ain` file.

This tool is intended for building source files that were decompiled using
[sys4dc](https://github.com/kichikuou/sys4dc).

## Installation

To build and install `sys4c` from source code, you need to have OCaml and opam
installed. Then, run the following commands:

```sh
$ git clone https://github.com/kichikuou/sys4c.git
$ cd sys4c
$ opam install . --deps-only
$ dune build
$ dune install
```

## Usage

First, decompile the `.ain` file using `sys4dc`:

```sh
$ sys4dc -o src SengokuRance.ain
```

Then, run `sys4c` to build the source files:

```sh
$ sys4c build src/SengokuRance.pje
```
