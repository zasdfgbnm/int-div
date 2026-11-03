# Integer Division

This Lake package is the executable Lean companion to Section 2 of *Algebraic
Properties of Integer Division*. It formalizes Euclidean, truncating, floor,
and ceiling quotient--remainder profiles over mathematical integers.

The package exposes one profile-parameterized statement for Table 1 and for
each numbered theorem. To use the complete paper-facing library, start a Lean
source file with:

```lean
module

import IntegerDivision
```

## Build

Install Lean through `elan`, then run:

```sh
lake build
lake lint
```

The checked-in `lean-toolchain` and `lake-manifest.json` pin the compiler and
all dependencies needed by this release.

## Modules

- `IntegerDivision.Prelude` defines the paper's shared predicates.
- `IntegerDivision.Semantics` defines the four division profiles and their
  quotient and remainder operations.
- `IntegerDivision.Specification` formalizes the two equivalent presentations
  in Table 1.
- `IntegerDivision.Paper` contains the canonical Section 2 theorem chain in
  publication order.

## Citation

When using this formalization, cite the accompanying paper and the exact
package release or commit used by your development.
