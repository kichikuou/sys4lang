# Patching an AIN

`sys4c patch` applies selected source changes to an existing AIN. Use it to:

- replace or add functions, methods, constructors, and destructors;
- add classes, structures, function types, and delegate types;
- add global groups, HLL libraries, and HLL functions;
- append globals and members to existing structures or classes; and
- change array sizes and initial values of global and member variables.

## Before you start

You need an AIN with a version below 8 and a PJE project containing the
declarations used by the patch. The project may be produced by `sys4dc`.

Keep a backup of the original AIN. While learning the command, write to a new
file with `-o` instead of updating the game's AIN directly.

Successful compilation does not guarantee compatibility with existing saves.
A save may resume in the middle of a function, so changing a function that was
active when the game was saved can make that save unusable. For example, for
saves made inside `main -> scene -> system.ResumeSave`, do not change `main` or
`scene`. See the System4 SDK
[ResumeSave restrictions](https://haniwa.technology/System4SDK/%E7%86%9F%E7%B7%B4%E8%80%85%E5%90%91%E3%81%91%E3%82%BB%E3%83%83%E3%83%88/%E3%83%9E%E3%83%8B%E3%83%A5%E3%82%A2%E3%83%AB/Sys42/html/lang/systemResumeSave_comment.html)
for details.

## Edit a decompiled function

The usual workflow is to edit a function in a project produced by `sys4dc`. If
needed, create the project with `sys4dc -o src game.ain`.

Open the generated JAF files, find the function to change, and edit its body.
For example:

```c
int calculate_score(int value)
{
    return value * 2;
}
```

Select the edited function by name when patching the original AIN:

```sh
sys4c patch src/game.pje calculate_score \
  --base-ain game.ain -o game-patched.ain
```

Only the selected function is replaced; other edited functions in the project
are not included. Check that the command reports `Replaced: calculate_score`,
then test `game-patched.ain` before installing it.

## Use a separate patch file

Suppose the base AIN already contains `calculate_score`, and the project
contains its declaration. Create `fixes.jaf` in the current directory to
replace that function and add a new helper named `adjust_score`. The file does
not need to be added to the PJE because it will be passed directly with
`--source`:

```c
int calculate_score(int renamed)
{
    return adjust_score(renamed);
}

int adjust_score(int value)
{
    return value * 2;
}
```

Run:

```sh
sys4c patch src/game.pje --base-ain game.ain \
  --source fixes.jaf -o game-patched.ain
```

The command should report `Replaced: calculate_score` and
`Added: adjust_score`. Review this list before testing: a misspelled existing
name is treated as a new function. A replacement may rename parameters, but its
return type, argument types, and argument count must match the base AIN.

When adding a method, constructor, or destructor, also add its declaration to
the corresponding class in the project.

## Select changes

Every patch command must select at least one target. You can select targets by
name, with `--source`, or with both:

| Selection | What it applies |
| --- | --- |
| Function or method name | Adds or replaces that function body |
| Constructor or destructor name | Adds or replaces that body |
| Class or structure name | Adds the type if new, or appends its new members if existing; rebuilds member-array initialization |
| Function type or delegate type name | Adds the type if new, or validates its existing signature |
| Global or global group name | Adds new global groups, appends all new trailing globals, and rebuilds initialization for all globals |
| HLL import name | Adds the library if new and appends its new functions |
| `--source FILE` | Selects function bodies, classes, structures, function types, delegate types, global groups, and non-const globals in a JAF file, or the library declared by an HLL file |

Use a positional name for a definition already present in the PJE, as in the
decompiled-function example above. Class functions use qualified names such as
`Counter::scaled`, `Counter::Counter`, and `Counter::~Counter`.

Use repeatable `--source` options for external patch files. Names and
`--source` options may be combined in one command.

Paths passed with `--source` are relative to the current directory. Source
paths inside the PJE are relative to the project and its `SourceDir`. All JAF
and HLL files use the encoding specified by the PJE.

`--base-ain` and `-o` default to the AIN named by the PJE's `OutputDir` and
`CodeName`. Omitting both therefore updates that AIN in place and does not make
a backup.

## Add globals or members

New globals must come after every existing global in the project declarations.
Existing globals must keep their name, type, order, and group. A new global may
be ungrouped or use an existing or new `globalgroup`. Global groups require
AIN version 5 or later. Empty groups can also be added by selecting their
name or passing their JAF file with `--source`.

Keep every existing global declaration in the project, including unchanged
ones. Then select any global or global group to add new globals and rebuild
global initialization:

```sh
sys4c patch src/game.pje new_score \
  --base-ain game.ain -o game-patched.ain
```

This rebuilds initialization for all globals, not just `new_score`.

New members must likewise come after every existing member in their class.
Existing members must keep their name, type, and order. Select the class to add
its trailing members and rebuild its member-array initialization:

```sh
sys4c patch src/game.pje Counter \
  --base-ain game.ain -o game-patched.ain
```

## Add HLL libraries or functions

Add the library declaration to the PJE, using the usual HLL file and import
name pair. For example:

```c
Source = {
    "API.hll", "API",
    "patch.jaf",
}
```

Declare the new functions in `API.hll`, then select the HLL import name along
with the JAF functions that call them:

```sh
sys4c patch src/game.pje API calculate_score \
  --base-ain game.ain -o game-patched.ain
```

Selecting an HLL adds the library if absent and appends all functions absent
from that library. Existing calls remain valid even if the HLL declarations
are reordered or omit existing functions. Existing signatures must match;
parameter names may change. New HLL declarations must be selected even if
they are unused.

You can also select an HLL file with `--source API.hll`. For a file already
in the PJE, its project import name is retained. An external HLL file uses
its filename without the extension as both the library and import name.
A patch containing only HLL additions is valid. The HLL implementation must
be available to the game engine; patching adds its declarations to the AIN.

## Add types

Select new types by name or with `--source`.

```c
struct Item {
    int value;
};

struct Container {
    Item item;
};

functype int Callback(ref Item item);
delegate void EventHandler(ref Container container);
```

If these declarations are in the PJE, select all four types:

```sh
sys4c patch src/game.pje Item Container Callback EventHandler \
  --base-ain game.ain -o game-patched.ain
```

Alternatively, pass the file with `--source`. A patch containing only type
additions is valid and reports entries such as `Added struct: Item` and
`Added functype: Callback`.

Every new type declared in the loaded sources must be explicitly selected,
even if unused. Dependencies are not selected automatically.

Selecting a class does not select its method, constructor, or destructor
bodies. If a new class declares any of these functions, also select their
bodies by qualified name or with `--source`. For example:

```sh
sys4c patch src/game.pje NewClass 'NewClass::method' \
  --base-ain game.ain -o game-patched.ain
```

A single `--source` selects both the class and its bodies if they are in that
file. For bodies defined in another file, select that file too, or select the
functions by name.

## Change array sizes

To change a member-array size, edit its normal declaration and select its
class. For example, after changing `array@int values[16];` in `Buffer` to
`array@int values[32];`, run:

```sh
sys4c patch src/game.pje Buffer \
  --base-ain game.ain -o game-patched.ain
```

For a global array, select any global. This rebuilds initialization for all
globals.

The change applies when new arrays are initialized. Objects and arrays in
existing saves are not resized or reinitialized.

## Apply another patch

Use the previous output as the base for the next patch. You do not need to
repeat an earlier `--source` option unless you want to replace those functions
again.

The project must contain declarations for additions that the new patch needs
to compile. This includes:

- a type, function, method, global, or member referenced by selected code; and
- globals or class members whose declarations are being extended again.

For example, if `second-fix.jaf` calls the previously added `adjust_score`, its
declaration must now be available from the project. Declarations for unrelated
earlier additions are not needed.

```sh
sys4c patch src/game.pje --base-ain game-patched.ain \
  --source second-fix.jaf -o game-patched-2.ain
```

## Debug information

If `debug_info.json` exists next to the PJE, `sys4c patch` updates it with
mappings for the appended code. Use the JSON that belongs to the base AIN,
especially when applying patches repeatedly. The command stops with an error
if the JSON contains mappings past the end of the base AIN code, for example
when a JSON already updated for a patched AIN is used with the original AIN.

If the file is missing, the command does not create or update it. Use
`--no-debug-info` when debug information is intentionally not needed.

## Limits

- AIN version 8 and later are unsupported. Scenario-label bodies and scenario
  jumps are supported only in AIN versions 2 through 7.
- Existing function and HLL function signatures cannot be changed.
- Existing globals and members cannot be removed, renamed, reordered, or have
  their types changed.
- Repeated patches increase the file size because old code and strings remain.
