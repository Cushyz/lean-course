# Lean Course

This repository contains Lean formalizations developed during the Lean course.

## Blueprint

The project blueprint is available at:

https://hilda-hyh.github.io/A-Lean-Formalization-of-Curve-Neighborhoods-for-the-Infinite-Dihedral-Group/
## Structure

- Lean entry point: `Dihedral.lean`
- Lean code: `Dihedral/`
- Executable finite model: `Dihedral/Computable.lean`
- Blueprint: `blueprint/`

## Build

Run the main library with:

```bash
lake build
```

The project is intended to build with the standard mathlib linter set enabled.

The lightweight executable/documentation examples live in
`Dihedral/Examples.lean` and can be checked separately with:

```bash
lake build Dihedral.Examples
```

The computable model provides `Ad_finset` and
`CurveNeighborhood_computable`, together with equivalence theorems
`coe_Ad_finset` and `coe_CurveNeighborhood_computable` relating the finite
objects to the Prop-valued definitions.
