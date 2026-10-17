# Patching an AIN

`sys4c patch` applies selected source changes to an existing AIN. Use it to:

- [replace or add functions and methods](#functions-and-methods);
- [add types](#types);
- [add members to existing classes](#classes);
- [add globals and global groups](#globals);
- change array sizes of [global](#globals) and [member](#classes) variables;
  and
- change [initial values of global variables](#globals).

## When to use it

### Keep saved games compatible

In System4, there are two ways to save a game:

- `system.GlobalSave` saves only the values of global variables. It is used in
  titles such as Sengoku Rance and Rance Quest.
- `system.ResumeSave` saves a snapshot of the virtual machine. This snapshot
  includes the addresses of the code currently being executed as well as the
  call stack. This feature is used, for example, in Rance 6 and Rance 9.

When a project created with `sys4dc` is recompiled using `sys4c build`, the new
AIN behaves the same as the original, but its bytecode is not identical. The
code addresses in a ResumeSave made with the original AIN do not point to the
same code in the new AIN, so the rebuilt game cannot load that save.

`sys4c patch` does not rebuild the AIN. It keeps the code that is already in
the AIN, and adds the new code after it. The patched game can load ResumeSaves
made with the original AIN, with the conditions in
[Saved games and when changes take effect](#saved-games-and-when-changes-take-effect).
If you are modifying a game that uses ResumeSave and need to maintain
compatibility with existing save data, use `sys4c patch`.

### Distribute a small change

A small change, such as a quality-of-life fix, can be distributed as one
[patch file](#use-a-patch-file). The patch file contains only the items that
the change needs, not the full decompiled project. Users can apply it to their
own AIN, so it is easy to combine with other mods.

## Quick start

You need an AIN and a PJE project. The usual workflow is to edit a function in
a project produced by `sys4dc`. If needed, create the project with
`sys4dc -o src game.ain`.

Open the generated JAF files, find the function to change, and edit its body.
For example, change `return value;` in `calculate_score` to:

```c
int calculate_score(int value)
{
    return value * 2;  // Patched: double the score
}
```

To patch the original AIN, select the edited function by name:

```sh
sys4c patch src/game.pje calculate_score -o game-patched.ain
```

Only the selected function is replaced; any other functions in the project that
have been edited are not included.

Without `-o`, the command overwrites the AIN specified by the project. In that
case, keep a backup of the original AIN.

## Select what to patch

Every patch command must select at least one target. There are three ways to
select targets:

- Write the name of a function or type on the command line, after the PJE path.
  Globals variables cannot be selected by name. Use a qualified name such as
  `Counter::scaled` for a method.
- Pass `--globals` to apply the [globals](#globals) in the project.
- Pass a [patch file](#use-a-patch-file) with `--source`.

The [selection table](#selection) shows what each selection applies.

### Use a patch file

A patch file is a JAF file passed with `--source`. It does not need to be added
to the PJE. For example, create `fixes.jaf` in the current directory to replace
`calculate_score` and add a new helper function `adjust_score`:

```c
int calculate_score(int value)
{
    return adjust_score(value);
}

int adjust_score(int value)
{
    return value * 2;
}
```

Run:

```sh
sys4c patch src/game.pje --source fixes.jaf -o game-patched.ain
```

`--source` selects every function and type in the file. If the file contains
global variables, it also acts as `--globals`. The option can be repeated.

An item in a patch file is used instead of the item of the same name in the
project. Two `--source` files cannot contain the same item. For example, the
same class in two patch files is an error.

With this, a patch file can contain all of its changes, and the project does
not need edits.

### Which to use

Edit the project when you maintain the decompiled project as the source of
truth. Use a patch file when you want to keep all changes of a patch in one
place, separate from the decompiled project.

## What you can change

### Functions and methods

If the base AIN does not already contain a given function or method, it is
added. Otherwise, it is replaced. The return type, as well as the number and
types of parameters, of the replacement function must match those of the
original AIN.

Select the function or method by name, or write it in a patch file.

When adding a method, it must be declared in its class. For example, to add
`void Foo::bar()`, also write the line `void bar();` in
`class Foo { ... }`. Either add the line to the class in the project, or
write the whole class again in a patch file. See [Classes](#classes).

### Types

New classes, function types, and delegate types can be added. Existing function
types and delegate types cannot be changed. For changes to existing classes,
see [Classes](#classes).

For example, suppose you add these three types:

```c
class Item {
    int value;
};

functype int Callback();
delegate void EventHandler();
```

If you add them to a JAF file in the project, write all three names on the
command line:

```sh
sys4c patch src/game.pje Item Callback EventHandler -o game-patched.ain
```

If you write them in a patch file, pass that file with `--source`. This
selects all the types in the file.

Selecting a class does not select its methods. If a new class has methods,
also select them by name or with `--source`. For example:

```sh
sys4c patch src/game.pje NewClass 'NewClass::method' -o game-patched.ain
```

### Classes

Selecting an existing class appends its new members and applies the array
sizes of its members.

New member variables must come after every existing member in their class.
Existing members must keep their name, type, and order.

For example, suppose that the project contains this class:

```c
class Foo {
public:
    int x;
    array@int arr[16];
    int baz(int n);
};
```

This change adds the member `y` and the method `bar`, and changes the
size of `arr`:

```c
class Foo {
public:
    int x;
    array@int arr[32];
    int y;
    int baz(int n);
    void bar();
};

void Foo::bar()
{
    x += y;
}
```

To make the change in the project, edit the class there, and select the class
and the new method by name:

```sh
sys4c patch src/game.pje Foo 'Foo::bar' -o game-patched.ain
```

To make the change in a patch file, copy the whole class from the project into
the patch file, change the copy there, and pass the file with `--source`. The
class in the patch file replaces the class in the project as a whole, including
its list of members and methods. Do not remove or reorder the existing members,
and do not remove the constructor. To make a constructor do nothing, replace it
with one that has an empty body.

### Globals

`--globals` adds new global groups, appends new globals, and sets the initial
values and array sizes of all globals from the project.

New globals must come after every existing global in the project. Existing
globals must keep their name, type, order, and group.

To change globals in the project, edit them and pass `--globals`:

```sh
sys4c patch src/game.pje --globals -o game-patched.ain
```

In a patch file, new globals are added after the project globals. A global that
is also in the project replaces the one in the project. It must be in the same
global group as in the project. For example, if the project contains
`int score = 0;`, this patch file changes the initial value of `score`:

```c
int score = 10;
```

## Saved games and when changes take effect

A patch does not change the code that is already in the base AIN. A change
takes effect only in the code that the patch adds.

A save may resume in the middle of a function. After the game loads a save,
the functions in its call stack continue to run the code of the base AIN until
they return. Only new calls run the replaced code. For example, for a save made
inside `main -> scene -> system.ResumeSave`, a change to `scene` takes effect
when `main` calls `scene` again.

`system.ResumeLoad` rejects a save if a function in its call stack has a
different CRC value, which is calculated from the code. With `--keep-crc`,
replaced functions keep their CRC values, so the game can load such saves.

A changed array size applies only to arrays created after the change. Objects
and arrays in existing saves keep their old sizes and values.

A changed constant or default argument value applies only to the code that the
patch compiles. Code in the base AIN keeps the old values.

## Workflows

### Patch a patched AIN

To make changes on top of an AIN that is already patched, decompile it with
`sys4dc` into a new directory, and patch it with the new project:

```sh
sys4dc -o src2 game-patched.ain
sys4c patch src2/game-patched.pje --source more-fixes.jaf -o game-patched-2.ain
```

### Debug information

With `--debug-info`, `sys4c patch` reads `debug_info.json` next to the PJE and
updates it with mappings for the appended code.

The command updates `debug_info.json` in place, even when `-o` writes the AIN
to a new file. After that, the JSON belongs to the patched AIN, not to the
original. If you run the command with `--debug-info` on the original AIN
again, it stops with an error.

## Reference

### Command line

```sh
sys4c patch PROJECT [TARGET...] [OPTION...]
```

| Argument or option | Description |
| --- | --- |
| `PROJECT` | The PJE file |
| `TARGET` | Name of a function, method, class, function type, or delegate type to apply |
| `--source FILE` | A patch file to apply; can be repeated |
| `--globals` | Add new globals and global groups, and set the initial values of all globals from the project |
| `--keep-crc` | Keep the CRC values of the replaced functions |
| `--base-ain FILE` | The AIN to patch |
| `-o FILE`, `--output FILE` | The output AIN |
| `--debug-info` | Read and update `debug_info.json` |

`--base-ain` and `-o` default to the AIN specified by the PJE's `OutputDir` and
`CodeName`.

Paths passed with `--source` are relative to the current directory. All JAF files
use the encoding specified by the PJE.

### Selection

| Selection | What it applies |
| --- | --- |
| Function or method name | Adds or replaces that function |
| Class name | Adds the class if new, or appends its new members if existing; applies the array sizes of its members |
| Function type or delegate type name | Adds the type if new |
| `--globals` | Adds new global groups, appends new globals, and sets the initial values and array sizes of all globals from the project |
| `--source FILE` | Selects all functions and types in a JAF file; acts as `--globals` if the file contains globals; replaces the items with the same names in the project |

### Limits

- AIN version 0 and versions 9 and later are unsupported. Scenario-label
  bodies and scenario jumps cannot be patched in AIN version 1.
- HLL libraries and HLL functions cannot be added or changed.
- Repeated patches increase the file size because old code and strings remain.
