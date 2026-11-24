# Lean proof: right-handed ↔ left-handed conversion

Formal proofs for the paper in `../paper/main.tex`, written in Lean 4 with Mathlib
(`QuaternionHandedness/Basic.lean`).

Angles: φ about x, θ about y, ψ about z (right-handed system).

| Statement | Example 1 (mirrored z) | Example 2 (Unity3D, y/z swapped) |
|---|---|---|
| R_r, R_l closed forms | `Rr_explicit`, `Rl_explicit` | `R2r_explicit`, `R2l_explicit` |
| R_l = P R_r P | `Rl_eq_S_Rr_S` | `R2l_eq_P2_R2r_P2` |
| eul2quat closed forms | `qr_explicit`, `ql_explicit` | `q2r_explicit`, `q2l_explicit` |
| rotm2quat closed forms | `rotm2quat_Rr_explicit`, `rotm2quat_Rl_explicit` | – |
| rotm2quat = eul2quat (all 4 components) | `eul_eq_rotm_right`, `eul_eq_rotm_left` | `rotm2quat_R2r`, `rotm2quat_R2l` |
| quaternion rule right → left | `rotm2quat_left_eq_toLeft` | `rotm2quat_left2_eq_toLeft2` |
| quaternion rule left → right | `rotm2quat_right_eq_toLeft` | `rotm2quat_right2_eq_toLeft2` |
| position | `position_left` | `position_left2` |

Rules: Example 1 (q_s, q_x, q_y, q_z) ↔ (q_s, −q_x, −q_y, q_z) and (x, y, z) ↔ (x, y, −z);
Example 2 (q_s, q_x, q_y, q_z) ↔ (q_s, −q_x, −q_z, −q_y) and (x, y, z) ↔ (x, z, y).

Every rotm2quat statement assumes q_s > 0, the branch in which rotm2quat divides by 4 q_s.
The general theorem of the paper (arbitrary reflection P) is not formalized.

## Build

```sh
# requires elan (https://lean-lang.org/install/manual/)
lake exe cache get   # download prebuilt Mathlib
lake build
```
