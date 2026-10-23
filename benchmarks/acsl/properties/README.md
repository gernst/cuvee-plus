<!--
This file is part of the SV-Benchmarks collection of verification tasks:
https://github.com/sosy-lab/sv-benchmarks

SPDX-FileCopyrightText: 2011-2026 The SV-Benchmarks Community

SPDX-License-Identifier: Apache-2.0
-->

### Behavioral Specifications

There are several 'default' specifications that many people use:
  - [unreach-call](c/properties/unreach-call.prp):
    A certain function call must not be reachable in the program.
  - [valid-memsafety, valid-deref, valid-free, valid-memtrack](c/properties/valid-memsafety.prp):
    A certain memory safety property must hold in the program.
    "memsafety" is the conjunction the other three properties.
  - [valid-memcleanup](c/properties/valid-memcleanup.prp):
    All allocated memory must be deallocated before the program terminates (note that this is stronger then avoiding memory leaks).
  - [no-overflow](c/properties/no-overflow.prp):
    A certain kind of undefined behavior (overflows of signed ints) must not be present in the program.
  - [termination](c/properties/termination.prp):
    The program must terminate on all execution paths.
  - [no-data-race](c/properties/no-data-race.prp):
    The program must be free of data races.

The above specifications are used, e.g., by SV-COMP.

### Test Specifications

The following are some 'default' specifications that many people use for test-case generation:
  - [coverage-branches](c/properties/coverage-branches.prp):
    The generated test suite should cover all branches of the program.
  - [coverage-error-call](c/properties/coverage-error-call.prp):
    The generated test suite should contain (at least) one test case that covers the call of a certain function.

The above test specifications are used, e.g., by Test-Comp.
