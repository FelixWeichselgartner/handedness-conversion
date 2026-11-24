# Handedness Conversion

Converting poses between right-handed and left-handed coordinate systems:
quaternions, Euler angles and rotation matrices.

This repository contains a short paper and a formal proof in Lean 4.

## The rule

If the coordinates of a left-handed system are obtained from a right-handed system by an
orthogonal matrix `P` with `det P = -1` (`p_l = P p_r`), then

| Quantity | Conversion |
|---|---|
| Position | `t_l = P t_r` |
| Rotation matrix | `R_l = P R_r Pᵀ` |
| Quaternion `q = (q_s, v)` | `q_l = (q_s, -P v)` |

The scalar part stays the same, the vector part is transformed with `-P`. If `P` is symmetric
(mirroring one axis, or swapping two axes), the rule is its own inverse.

| Case | Quaternion | Position |
|---|---|---|
| Mirrored z axis | `(q_s, q_x, q_y, q_z) ↔ (q_s, -q_x, -q_y, q_z)` | `(x, y, z) ↔ (x, y, -z)` |
| Unity3D (y and z swapped) | `(q_s, q_x, q_y, q_z) ↔ (q_s, -q_x, -q_z, -q_y)` | `(x, y, z) ↔ (x, z, y)` |

A common mistake is to permute the vector part like a position without changing its sign.
This gives the inverse rotation.

## Contents

| Folder | Content |
|---|---|
| [`paper/`](paper/) | LaTeX source and PDF of the paper |
| [`lean/`](lean/) | Lean 4 / Mathlib proofs of both cases |

## Build

Paper:

```sh
cd paper
latexmk -pdf main.tex
```

Lean proof (requires [elan](https://lean-lang.org/install/manual/)):

```sh
cd lean
lake exe cache get
lake build
```

## License

- Paper (`paper/main.tex`, `paper/main.pdf`, `paper/bibliography.bib`):
  [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/), see `paper/LICENSE`.
- Lean code (`lean/`) and everything else not listed below: MIT, see `LICENSE`.

## Third-party files

- `paper/arxiv.sty`: [arxiv-style](https://github.com/kourgeorge/arxiv-style) by George Kour,
  MIT License (see `paper/arxiv-style-LICENSE.txt`).
- `paper/IEEEtran.bst`, `paper/IEEEabrv.bib`: IEEEtran by Michael Shell, LaTeX Project
  Public License.
