# Lean Formalization of Affine Curve Neighborhoods

This repository contains a Lean 4 formalization of the rank-one combinatorial curve-neighborhood formula for the affine flag manifold of type `A_1^(1)`, modeled by the infinite dihedral group.  The formalized theorem is the combinatorial formula, not a construction of affine flag ind-schemes, loop groups, or stable-map moduli spaces.

The submitted JSSC artifact corresponds to release tag `v1.0-jssc-submission`.

## Blueprint

The project blueprint is available at:

https://hilda-hyh.github.io/lean-affine-curve-neighborhoods/

## Structure

- Lean entry point: `Dihedral.lean`
- Core Lean code: `Dihedral/`
- Main theorem: `Dihedral/CurveNeighborhood.lean`
- Executable finite model: `Dihedral/Computable.lean`
- Certified examples: `Dihedral/Examples.lean`
- Blueprint: `blueprint/`

## Main Declarations

The main curve-neighborhood formula is available as:

- `main_theorem`
- `curve_nbhd_eq_mul_max_ad`

The computable finite model is certified by:

- `CurveNeighborhood_computable`
- `mem_CurveNeighborhood_computable_iff`
- `coe_CurveNeighborhood_computable`

The executable search space has explicit linear bounds:

- `length_enumerateD_list`
- `card_enumerateD_le`
- `card_Ad_finset_le`

The example suite includes theorem-backed balanced, unbalanced, translated rotation-base, and translated reflection-base cases.

## Build

Run the main library with:

```bash
lake build
```

The examples can be checked separately with:

```bash
lake build Dihedral.Examples
```

The artifact audit commands used in the manuscript are:

```bash
rg -n "\b(sorry|admit)\b" Dihedral Dihedral.lean
rg -n "\b(axiom|unsafe|set_option|noncomputable)\b" Dihedral Dihedral.lean
```

Both commands are expected to produce no matches in the project files listed above.
