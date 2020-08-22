# TLC

This repository contains the Coq implementation of the Temporal Logic
of Composable Distributed Components.

## Requirements

- Coq 8.12 or newer
- SSReflect 1.7 or newer

Additionally, to use the included makefile, the tools used in makefiles
produced by `coq_makefile` are required.  These tools are typically
present on Linux and macOS.  On Windows, MSYS, Cygwin, or WSL must be
used.

## Building

To build, run `make` in the `tlc` subdirectory:

```
$ cd path/to/clone/tlc
$ make
```

## Structure

Each subdirectory under `tlc` contains a logical module of files.  Each
source file contains a header describing the purpose and scope of the
file.  Each logical module contains a file named `all_<module>.v`, which
exports the entire module and contains a high-level description of the
module.


The `doc` directory contains a document describing the techniques used
in implementing the framework.
