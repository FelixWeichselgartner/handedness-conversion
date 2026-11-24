/-
Formal proofs for the paper ../paper/main.tex (Example 1: mirrored z axis,
Example 2 further below: Unity3D, y and z swapped).

Index convention of the LaTeX file:
  1 ↔ φ (rotation about x),  2 ↔ θ (rotation about y),  3 ↔ ψ (rotation about z)
  c_k = cos, s_k = sin of the full angle, c_kh / s_kh of the half angle.

Proved here (for all four quaternion components, not only q_s):
  * `Rr_explicit`, `Rl_explicit`        : closed forms of R_r and R_l (YXZ convention)
  * `qr_explicit`, `ql_explicit`        : eul2quat, closed forms of q_r and q_l
  * `rotm2quat_Rr_explicit`, `..._Rl_..`: rotm2quat, closed forms (sqrt / 4 q_s)
  * `eul_eq_rotm_right`, `eul_eq_rotm_left` : q_eul = q_rotm, all four components
  * `Rl_eq_S_Rr_S`                      : R_l = S R_r S with S = diag(1, 1, -1)
  * `rotm2quat_left_eq_toLeft`          : (q_s, q_x, q_y, q_z) ↦ (q_s, -q_x, -q_y, q_z)
  * `position_left`                     : (x, y, z) ↦ (x, y, -z)

Proof idea: every rotation matrix here is the image of a quaternion under the
(homogeneous) map `rotmOf`, which is multiplicative. rotm2quat inverts `rotmOf` on
unit quaternions with positive real part. Mirroring z is conjugation by S on matrices
and `toLeft` on quaternions, and both commute with `rotmOf`.
-/
import Mathlib

open Real

noncomputable section

namespace Handedness

/-! ## Quaternion helpers -/

/-- Quaternion `a + b i + c j + d k`. -/
def quat (a b c d : ℝ) : Quaternion ℝ := QuaternionAlgebra.mk a b c d

@[simp] lemma quat_re (a b c d : ℝ) : (quat a b c d).re = a := rfl
@[simp] lemma quat_imI (a b c d : ℝ) : (quat a b c d).imI = b := rfl
@[simp] lemma quat_imJ (a b c d : ℝ) : (quat a b c d).imJ = c := rfl
@[simp] lemma quat_imK (a b c d : ℝ) : (quat a b c d).imK = d := rfl

lemma quat_eta (p : Quaternion ℝ) : quat p.re p.imI p.imJ p.imK = p := rfl

lemma qext {p q : Quaternion ℝ} (h1 : p.re = q.re) (h2 : p.imI = q.imI)
    (h3 : p.imJ = q.imJ) (h4 : p.imK = q.imK) : p = q := by
  exact QuaternionAlgebra.ext h1 h2 h3 h4

/-- Hamilton product in coordinates. -/
lemma quat_mul (a b c d e f g h : ℝ) :
    quat a b c d * quat e f g h =
      quat (a * e - b * f - c * g - d * h) (a * f + b * e + c * h - d * g)
        (a * g - b * h + c * e + d * f) (a * h + b * g - c * f + d * e) := by
  apply qext <;> simp

/-- Squared norm. -/
def nsq (q : Quaternion ℝ) : ℝ := q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2

/-- Right-handed → left-handed (z mirrored): `(q_s, q_x, q_y, q_z) ↦ (q_s, -q_x, -q_y, q_z)`. -/
def toLeft (q : Quaternion ℝ) : Quaternion ℝ := quat q.re (-q.imI) (-q.imJ) q.imK

lemma toLeft_quat (a b c d : ℝ) : toLeft (quat a b c d) = quat a (-b) (-c) d := rfl

lemma toLeft_mul (p q : Quaternion ℝ) : toLeft (p * q) = toLeft p * toLeft q := by
  rw [← quat_eta p, ← quat_eta q]
  simp only [quat_mul, toLeft_quat]
  congr 1 <;> ring

/-- Mirroring twice is the identity, so the rule works in both directions. -/
lemma toLeft_toLeft (q : Quaternion ℝ) : toLeft (toLeft q) = q := by
  apply qext <;> simp [toLeft]

lemma nsq_toLeft (q : Quaternion ℝ) : nsq (toLeft q) = nsq q := by
  simp only [nsq, toLeft, quat_re, quat_imI, quat_imJ, quat_imK]
  ring

/-! ## Matrix helpers -/

lemma m3_congr {a b c d e f g h i a' b' c' d' e' f' g' h' i' : ℝ}
    (h1 : a = a') (h2 : b = b') (h3 : c = c') (h4 : d = d') (h5 : e = e')
    (h6 : f = f') (h7 : g = g') (h8 : h = h') (h9 : i = i') :
    !![a, b, c; d, e, f; g, h, i] = !![a', b', c'; d', e', f'; g', h', i'] := by
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9
  rfl

/-- Rotation matrix of a quaternion (homogeneous form, equals R(q) for |q| = 1). -/
def rotmOf (q : Quaternion ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![q.re ^ 2 + q.imI ^ 2 - q.imJ ^ 2 - q.imK ^ 2, 2 * (q.imI * q.imJ - q.re * q.imK),
      2 * (q.imI * q.imK + q.re * q.imJ);
    2 * (q.imI * q.imJ + q.re * q.imK), q.re ^ 2 - q.imI ^ 2 + q.imJ ^ 2 - q.imK ^ 2,
      2 * (q.imJ * q.imK - q.re * q.imI);
    2 * (q.imI * q.imK - q.re * q.imJ), 2 * (q.imJ * q.imK + q.re * q.imI),
      q.re ^ 2 - q.imI ^ 2 - q.imJ ^ 2 + q.imK ^ 2]

theorem rotmOf_mul (p q : Quaternion ℝ) : rotmOf (p * q) = rotmOf p * rotmOf q := by
  rw [← quat_eta p, ← quat_eta q]
  simp only [quat_mul, rotmOf, quat_re, quat_imI, quat_imJ, quat_imK]
  rw [Matrix.mul_fin_three]
  apply m3_congr <;> ring1

/-- Mirror of the z axis. -/
def S : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 1, 0; 0, 0, -1]

theorem S_rotmOf_S (q : Quaternion ℝ) : S * rotmOf q * S = rotmOf (toLeft q) := by
  simp only [S, rotmOf, toLeft, quat_re, quat_imI, quat_imJ, quat_imK]
  rw [Matrix.mul_fin_three, Matrix.mul_fin_three]
  apply m3_congr <;> ring1

/-! ## rotm2quat -/

/-- Scalar part from the trace. -/
def qsOf (R : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := Real.sqrt (1 + R 0 0 + R 1 1 + R 2 2) / 2

/-- Standard rotm2quat (branch q_s > 0). -/
def rotm2quat (R : Matrix (Fin 3) (Fin 3) ℝ) : Quaternion ℝ :=
  quat (qsOf R) ((R 2 1 - R 1 2) / (4 * qsOf R)) ((R 0 2 - R 2 0) / (4 * qsOf R))
    ((R 1 0 - R 0 1) / (4 * qsOf R))

lemma rotm2quat_of (a b c d e f g h i : ℝ) :
    rotm2quat !![a, b, c; d, e, f; g, h, i] =
      quat (Real.sqrt (1 + a + e + i) / 2)
        ((h - f) / (4 * (Real.sqrt (1 + a + e + i) / 2)))
        ((c - g) / (4 * (Real.sqrt (1 + a + e + i) / 2)))
        ((d - b) / (4 * (Real.sqrt (1 + a + e + i) / 2))) := by
  rfl

/-- rotm2quat inverts `rotmOf` on unit quaternions with positive scalar part. -/
theorem rotm2quat_rotmOf (q : Quaternion ℝ) (hq : nsq q = 1) (hw : 0 < q.re) :
    rotm2quat (rotmOf q) = q := by
  rw [rotmOf, rotm2quat_of]
  have hs : Real.sqrt (1 + (q.re ^ 2 + q.imI ^ 2 - q.imJ ^ 2 - q.imK ^ 2)
      + (q.re ^ 2 - q.imI ^ 2 + q.imJ ^ 2 - q.imK ^ 2)
      + (q.re ^ 2 - q.imI ^ 2 - q.imJ ^ 2 + q.imK ^ 2)) / 2 = q.re := by
    have h4 : 1 + (q.re ^ 2 + q.imI ^ 2 - q.imJ ^ 2 - q.imK ^ 2)
        + (q.re ^ 2 - q.imI ^ 2 + q.imJ ^ 2 - q.imK ^ 2)
        + (q.re ^ 2 - q.imI ^ 2 - q.imJ ^ 2 + q.imK ^ 2) = (2 * q.re) ^ 2 := by
      unfold nsq at hq
      linear_combination -hq
    rw [h4, Real.sqrt_sq (by linarith)]
    ring
  rw [hs]
  have hne : 4 * q.re ≠ 0 := by
    intro h
    linarith
  apply qext
  · rfl
  · rw [quat_imI, div_eq_iff hne]; ring
  · rw [quat_imJ, div_eq_iff hne]; ring
  · rw [quat_imK, div_eq_iff hne]; ring

/-! ## Elementary rotations (right-handed) and their quaternions -/

def Rx (φ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, cos φ, -sin φ; 0, sin φ, cos φ]
def Ry (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![cos θ, 0, sin θ; 0, 1, 0; -sin θ, 0, cos θ]
def Rz (ψ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![cos ψ, -sin ψ, 0; sin ψ, cos ψ, 0; 0, 0, 1]

def qx (φ : ℝ) : Quaternion ℝ := quat (cos (φ / 2)) (sin (φ / 2)) 0 0
def qy (θ : ℝ) : Quaternion ℝ := quat (cos (θ / 2)) 0 (sin (θ / 2)) 0
def qz (ψ : ℝ) : Quaternion ℝ := quat (cos (ψ / 2)) 0 0 (sin (ψ / 2))

lemma cos_half (x : ℝ) : cos x = cos (x / 2) ^ 2 - sin (x / 2) ^ 2 := by
  have h1 : cos x = cos (2 * (x / 2)) := by congr 1; ring
  have h2 := Real.sin_sq_add_cos_sq (x / 2)
  rw [h1, Real.cos_two_mul]
  linarith

lemma sin_half (x : ℝ) : sin x = 2 * sin (x / 2) * cos (x / 2) := by
  have h1 : sin x = sin (2 * (x / 2)) := by congr 1; ring
  rw [h1, Real.sin_two_mul]

theorem Rx_eq (φ : ℝ) : Rx φ = rotmOf (qx φ) := by
  have h := Real.sin_sq_add_cos_sq (φ / 2)
  rw [Rx, cos_half φ, sin_half φ]
  simp only [rotmOf, qx, quat_re, quat_imI, quat_imJ, quat_imK]
  apply m3_congr <;> first | ring1 | linear_combination -h

theorem Ry_eq (θ : ℝ) : Ry θ = rotmOf (qy θ) := by
  have h := Real.sin_sq_add_cos_sq (θ / 2)
  rw [Ry, cos_half θ, sin_half θ]
  simp only [rotmOf, qy, quat_re, quat_imI, quat_imJ, quat_imK]
  apply m3_congr <;> first | ring1 | linear_combination -h

theorem Rz_eq (ψ : ℝ) : Rz ψ = rotmOf (qz ψ) := by
  have h := Real.sin_sq_add_cos_sq (ψ / 2)
  rw [Rz, cos_half ψ, sin_half ψ]
  simp only [rotmOf, qz, quat_re, quat_imI, quat_imJ, quat_imK]
  apply m3_congr <;> first | ring1 | linear_combination -h

lemma qx_neg (φ : ℝ) : qx (-φ) = toLeft (qx φ) := by
  simp only [qx, toLeft_quat, neg_div, Real.cos_neg, Real.sin_neg, neg_zero]

lemma qy_neg (θ : ℝ) : qy (-θ) = toLeft (qy θ) := by
  simp only [qy, toLeft_quat, neg_div, Real.cos_neg, Real.sin_neg, neg_zero]

lemma qz_toLeft (ψ : ℝ) : toLeft (qz ψ) = qz ψ := by
  simp only [qz, toLeft_quat, neg_zero]

/-! ## The example: YXZ convention -/

variable (θ φ ψ : ℝ)

/-- R_r = R_y(θ) R_x(φ) R_z(ψ). -/
def Rr : Matrix (Fin 3) (Fin 3) ℝ := Ry θ * Rx φ * Rz ψ
/-- R_l = R_y(-θ) R_x(-φ) R_z(ψ). -/
def Rl : Matrix (Fin 3) (Fin 3) ℝ := Ry (-θ) * Rx (-φ) * Rz ψ
/-- q_{r,eul2quat} = q_y(θ) q_x(φ) q_z(ψ). -/
def qr : Quaternion ℝ := qy θ * qx φ * qz ψ
/-- q_{l,eul2quat} = q_y(-θ) q_x(-φ) q_z(ψ). -/
def ql : Quaternion ℝ := qy (-θ) * qx (-φ) * qz ψ

/-- Closed form of R_r (matrix in the LaTeX file). -/
theorem Rr_explicit : Rr θ φ ψ =
    !![cos ψ * cos θ + sin φ * sin ψ * sin θ, cos ψ * sin φ * sin θ - cos θ * sin ψ,
        cos φ * sin θ;
      cos φ * sin ψ, cos φ * cos ψ, -sin φ;
      cos θ * sin φ * sin ψ - cos ψ * sin θ, sin ψ * sin θ + cos ψ * cos θ * sin φ,
        cos φ * cos θ] := by
  simp only [Rr, Ry, Rx, Rz]
  rw [Matrix.mul_fin_three, Matrix.mul_fin_three]
  apply m3_congr <;> ring1

/-- Closed form of R_l. Entry (3,3) is `c₁c₂`; the LaTeX file has the typo `c₁c₃`. -/
theorem Rl_explicit : Rl θ φ ψ =
    !![cos ψ * cos θ + sin φ * sin ψ * sin θ, cos ψ * sin φ * sin θ - cos θ * sin ψ,
        -(cos φ * sin θ);
      cos φ * sin ψ, cos φ * cos ψ, sin φ;
      cos ψ * sin θ - cos θ * sin φ * sin ψ, -(sin ψ * sin θ) - cos ψ * cos θ * sin φ,
        cos φ * cos θ] := by
  simp only [Rl, Ry, Rx, Rz, Real.cos_neg, Real.sin_neg]
  rw [Matrix.mul_fin_three, Matrix.mul_fin_three]
  apply m3_congr <;> ring1

/-- eul2quat, right-handed, all four components. -/
theorem qr_explicit : qr θ φ ψ =
    quat (sin (φ / 2) * sin (ψ / 2) * sin (θ / 2) + cos (φ / 2) * cos (ψ / 2) * cos (θ / 2))
      (cos (ψ / 2) * cos (θ / 2) * sin (φ / 2) + cos (φ / 2) * sin (ψ / 2) * sin (θ / 2))
      (cos (φ / 2) * cos (ψ / 2) * sin (θ / 2) - cos (θ / 2) * sin (φ / 2) * sin (ψ / 2))
      (cos (φ / 2) * cos (θ / 2) * sin (ψ / 2) - cos (ψ / 2) * sin (φ / 2) * sin (θ / 2)) := by
  simp only [qr, qx, qy, qz]
  rw [quat_mul, quat_mul]
  congr 1 <;> ring1

/-- Structural form of the handedness rule for eul2quat. -/
theorem ql_eq_toLeft : ql θ φ ψ = toLeft (qr θ φ ψ) := by
  rw [ql, qr, toLeft_mul, toLeft_mul, qy_neg, qx_neg, qz_toLeft]

/-- eul2quat, left-handed, all four components. -/
theorem ql_explicit : ql θ φ ψ =
    quat (sin (φ / 2) * sin (ψ / 2) * sin (θ / 2) + cos (φ / 2) * cos (ψ / 2) * cos (θ / 2))
      (-(cos (ψ / 2) * cos (θ / 2) * sin (φ / 2)) - cos (φ / 2) * sin (ψ / 2) * sin (θ / 2))
      (cos (θ / 2) * sin (φ / 2) * sin (ψ / 2) - cos (φ / 2) * cos (ψ / 2) * sin (θ / 2))
      (cos (φ / 2) * cos (θ / 2) * sin (ψ / 2) - cos (ψ / 2) * sin (φ / 2) * sin (θ / 2)) := by
  rw [ql_eq_toLeft, qr_explicit, toLeft_quat]
  congr 1 <;> ring1

theorem nsq_qr : nsq (qr θ φ ψ) = 1 := by
  rw [qr_explicit]
  simp only [nsq, quat_re, quat_imI, quat_imJ, quat_imK]
  have h1 := Real.sin_sq_add_cos_sq (φ / 2)
  have h2 := Real.sin_sq_add_cos_sq (θ / 2)
  have h3 := Real.sin_sq_add_cos_sq (ψ / 2)
  linear_combination
    ((sin (θ / 2) ^ 2 + cos (θ / 2) ^ 2) * (sin (ψ / 2) ^ 2 + cos (ψ / 2) ^ 2)) * h1
      + (sin (ψ / 2) ^ 2 + cos (ψ / 2) ^ 2) * h2 + h3

theorem Rr_eq_rotmOf : Rr θ φ ψ = rotmOf (qr θ φ ψ) := by
  rw [Rr, qr, rotmOf_mul, rotmOf_mul, Rx_eq, Ry_eq, Rz_eq]

theorem Rl_eq_rotmOf : Rl θ φ ψ = rotmOf (ql θ φ ψ) := by
  rw [Rl, ql, rotmOf_mul, rotmOf_mul, Rx_eq, Ry_eq, Rz_eq]

/-- Mirroring z: R_l = S R_r S. -/
theorem Rl_eq_S_Rr_S : Rl θ φ ψ = S * Rr θ φ ψ * S := by
  rw [Rl_eq_rotmOf, Rr_eq_rotmOf, S_rotmOf_S, ql_eq_toLeft]

/-! ### rotm2quat closed forms (LaTeX: q_{rotm2quat}) -/

/-- q_{s,rotm} = √(c₁c₃ + c₁c₂ + c₃c₂ + s₁s₃s₂ + 1) / 2, same for both systems. -/
def qsR : ℝ :=
  Real.sqrt (cos φ * cos ψ + cos φ * cos θ + cos ψ * cos θ + sin φ * sin ψ * sin θ + 1) / 2

theorem rotm2quat_Rr_explicit : rotm2quat (Rr θ φ ψ) =
    quat (qsR θ φ ψ)
      ((sin φ + sin ψ * sin θ + cos ψ * cos θ * sin φ) / (4 * qsR θ φ ψ))
      ((cos φ * sin θ + cos ψ * sin θ - cos θ * sin φ * sin ψ) / (4 * qsR θ φ ψ))
      ((cos φ * sin ψ + cos θ * sin ψ - cos ψ * sin φ * sin θ) / (4 * qsR θ φ ψ)) := by
  have harg : 1 + (cos ψ * cos θ + sin φ * sin ψ * sin θ) + cos φ * cos ψ + cos φ * cos θ
      = cos φ * cos ψ + cos φ * cos θ + cos ψ * cos θ + sin φ * sin ψ * sin θ + 1 := by ring
  unfold qsR
  rw [Rr_explicit, rotm2quat_of, harg]
  congr 1 <;> congr 1 <;> ring1

theorem rotm2quat_Rl_explicit : rotm2quat (Rl θ φ ψ) =
    quat (qsR θ φ ψ)
      (-(sin φ + sin ψ * sin θ + cos ψ * cos θ * sin φ) / (4 * qsR θ φ ψ))
      (-(cos φ * sin θ + cos ψ * sin θ - cos θ * sin φ * sin ψ) / (4 * qsR θ φ ψ))
      ((cos φ * sin ψ + cos θ * sin ψ - cos ψ * sin φ * sin θ) / (4 * qsR θ φ ψ)) := by
  have harg : 1 + (cos ψ * cos θ + sin φ * sin ψ * sin θ) + cos φ * cos ψ + cos φ * cos θ
      = cos φ * cos ψ + cos φ * cos θ + cos ψ * cos θ + sin φ * sin ψ * sin θ + 1 := by ring
  unfold qsR
  rw [Rl_explicit, rotm2quat_of, harg]
  congr 1 <;> congr 1 <;> ring1

/-! ### Main results -/

/-- Assumption of the rotm2quat branch: q_{s,eul} > 0. -/
abbrev QsPos : Prop :=
  0 < sin (φ / 2) * sin (ψ / 2) * sin (θ / 2) + cos (φ / 2) * cos (ψ / 2) * cos (θ / 2)

lemma qr_re_pos (h : QsPos θ φ ψ) : 0 < (qr θ φ ψ).re := by
  rw [qr_explicit]; exact h

/-- q_{r,rotm2quat} = q_{r,eul2quat}. -/
theorem rotm2quat_Rr (h : QsPos θ φ ψ) : rotm2quat (Rr θ φ ψ) = qr θ φ ψ := by
  rw [Rr_eq_rotmOf]
  exact rotm2quat_rotmOf _ (nsq_qr θ φ ψ) (qr_re_pos θ φ ψ h)

/-- q_{l,rotm2quat} = q_{l,eul2quat}. -/
theorem rotm2quat_Rl (h : QsPos θ φ ψ) : rotm2quat (Rl θ φ ψ) = ql θ φ ψ := by
  rw [Rl_eq_rotmOf]
  apply rotm2quat_rotmOf
  · rw [ql_eq_toLeft, nsq_toLeft, nsq_qr]
  · rw [ql_eq_toLeft]; exact qr_re_pos θ φ ψ h

/-- q_eul = q_rotm in the right-handed system, all four components. -/
theorem eul_eq_rotm_right (h : QsPos θ φ ψ) :
    qsR θ φ ψ
        = sin (φ / 2) * sin (ψ / 2) * sin (θ / 2) + cos (φ / 2) * cos (ψ / 2) * cos (θ / 2) ∧
    (sin φ + sin ψ * sin θ + cos ψ * cos θ * sin φ) / (4 * qsR θ φ ψ)
        = cos (ψ / 2) * cos (θ / 2) * sin (φ / 2) + cos (φ / 2) * sin (ψ / 2) * sin (θ / 2) ∧
    (cos φ * sin θ + cos ψ * sin θ - cos θ * sin φ * sin ψ) / (4 * qsR θ φ ψ)
        = cos (φ / 2) * cos (ψ / 2) * sin (θ / 2) - cos (θ / 2) * sin (φ / 2) * sin (ψ / 2) ∧
    (cos φ * sin ψ + cos θ * sin ψ - cos ψ * sin φ * sin θ) / (4 * qsR θ φ ψ)
        = cos (φ / 2) * cos (θ / 2) * sin (ψ / 2) - cos (ψ / 2) * sin (φ / 2) * sin (θ / 2) := by
  have e := rotm2quat_Rr θ φ ψ h
  rw [rotm2quat_Rr_explicit, qr_explicit] at e
  exact ⟨congrArg (fun q : Quaternion ℝ => q.re) e, congrArg (fun q : Quaternion ℝ => q.imI) e,
    congrArg (fun q : Quaternion ℝ => q.imJ) e, congrArg (fun q : Quaternion ℝ => q.imK) e⟩

/-- q_eul = q_rotm in the left-handed system, all four components. -/
theorem eul_eq_rotm_left (h : QsPos θ φ ψ) :
    qsR θ φ ψ
        = sin (φ / 2) * sin (ψ / 2) * sin (θ / 2) + cos (φ / 2) * cos (ψ / 2) * cos (θ / 2) ∧
    -(sin φ + sin ψ * sin θ + cos ψ * cos θ * sin φ) / (4 * qsR θ φ ψ)
        = -(cos (ψ / 2) * cos (θ / 2) * sin (φ / 2)) - cos (φ / 2) * sin (ψ / 2) * sin (θ / 2) ∧
    -(cos φ * sin θ + cos ψ * sin θ - cos θ * sin φ * sin ψ) / (4 * qsR θ φ ψ)
        = cos (θ / 2) * sin (φ / 2) * sin (ψ / 2) - cos (φ / 2) * cos (ψ / 2) * sin (θ / 2) ∧
    (cos φ * sin ψ + cos θ * sin ψ - cos ψ * sin φ * sin θ) / (4 * qsR θ φ ψ)
        = cos (φ / 2) * cos (θ / 2) * sin (ψ / 2) - cos (ψ / 2) * sin (φ / 2) * sin (θ / 2) := by
  have e := rotm2quat_Rl θ φ ψ h
  rw [rotm2quat_Rl_explicit, ql_explicit] at e
  exact ⟨congrArg (fun q : Quaternion ℝ => q.re) e, congrArg (fun q : Quaternion ℝ => q.imI) e,
    congrArg (fun q : Quaternion ℝ => q.imJ) e, congrArg (fun q : Quaternion ℝ => q.imK) e⟩

/-- Final rule of the section: q_l = (q_s, -q_x, -q_y, q_z) of q_r. -/
theorem rotm2quat_left_eq_toLeft (h : QsPos θ φ ψ) :
    rotm2quat (Rl θ φ ψ) = toLeft (rotm2quat (Rr θ φ ψ)) := by
  rw [rotm2quat_Rl θ φ ψ h, rotm2quat_Rr θ φ ψ h, ql_eq_toLeft]

/-- Reverse direction: left → right uses the same rule. -/
theorem rotm2quat_right_eq_toLeft (h : QsPos θ φ ψ) :
    rotm2quat (Rr θ φ ψ) = toLeft (rotm2quat (Rl θ φ ψ)) := by
  rw [rotm2quat_left_eq_toLeft θ φ ψ h, toLeft_toLeft]

theorem rotm2quat_left_components (h : QsPos θ φ ψ) :
    let q_r := rotm2quat (Rr θ φ ψ)
    let q_l := rotm2quat (Rl θ φ ψ)
    q_l.re = q_r.re ∧ q_l.imI = -q_r.imI ∧ q_l.imJ = -q_r.imJ ∧ q_l.imK = q_r.imK := by
  intro q_r q_l
  have e : q_l = toLeft q_r := rotm2quat_left_eq_toLeft θ φ ψ h
  rw [e]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Position: t_l = S t_r, i.e. (x, y, z) ↦ (x, y, -z). -/
theorem position_left (x y z : ℝ) : S.mulVec ![x, y, z] = ![x, y, -z] := by
  ext i
  fin_cases i <;> simp [S, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-! ## Example 2 (Unity): y and z axes swapped

Right-handed angles θ (y), φ (x), ψ (z); R_2r = R_z(ψ) R_x(φ) R_y(θ).
Left-handed system: R_2l = R_y(-ψ) R_x(-φ) R_z(-θ). -/

/-- Swap of y and z (a reflection, det = -1). -/
def P2 : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 0, 1; 0, 1, 0]

/-- `(q_s, q_x, q_y, q_z) ↦ (q_s, -q_x, -q_z, -q_y)`. -/
def toLeft2 (q : Quaternion ℝ) : Quaternion ℝ := quat q.re (-q.imI) (-q.imK) (-q.imJ)

lemma toLeft2_quat (a b c d : ℝ) : toLeft2 (quat a b c d) = quat a (-b) (-d) (-c) := rfl

lemma toLeft2_mul (p q : Quaternion ℝ) : toLeft2 (p * q) = toLeft2 p * toLeft2 q := by
  rw [← quat_eta p, ← quat_eta q]
  simp only [quat_mul, toLeft2_quat]
  congr 1 <;> ring

lemma toLeft2_toLeft2 (q : Quaternion ℝ) : toLeft2 (toLeft2 q) = q := by
  apply qext <;> simp [toLeft2]

lemma nsq_toLeft2 (q : Quaternion ℝ) : nsq (toLeft2 q) = nsq q := by
  simp only [nsq, toLeft2, quat_re, quat_imI, quat_imJ, quat_imK]
  ring

theorem P2_rotmOf_P2 (q : Quaternion ℝ) : P2 * rotmOf q * P2 = rotmOf (toLeft2 q) := by
  simp only [P2, rotmOf, toLeft2, quat_re, quat_imI, quat_imJ, quat_imK]
  rw [Matrix.mul_fin_three, Matrix.mul_fin_three]
  apply m3_congr <;> ring1

lemma nsq_mul (p q : Quaternion ℝ) : nsq (p * q) = nsq p * nsq q := by
  rw [← quat_eta p, ← quat_eta q, quat_mul]
  simp only [nsq, quat_re, quat_imI, quat_imJ, quat_imK]
  ring

lemma nsq_qx (φ : ℝ) : nsq (qx φ) = 1 := by
  simp only [nsq, qx, quat_re, quat_imI, quat_imJ, quat_imK]
  linear_combination Real.sin_sq_add_cos_sq (φ / 2)

lemma nsq_qy (θ : ℝ) : nsq (qy θ) = 1 := by
  simp only [nsq, qy, quat_re, quat_imI, quat_imJ, quat_imK]
  linear_combination Real.sin_sq_add_cos_sq (θ / 2)

lemma nsq_qz (ψ : ℝ) : nsq (qz ψ) = 1 := by
  simp only [nsq, qz, quat_re, quat_imI, quat_imJ, quat_imK]
  linear_combination Real.sin_sq_add_cos_sq (ψ / 2)

lemma qy_neg_toLeft2 (ψ : ℝ) : qy (-ψ) = toLeft2 (qz ψ) := by
  simp only [qy, qz, toLeft2_quat, neg_div, Real.cos_neg, Real.sin_neg, neg_zero]

lemma qx_neg_toLeft2 (φ : ℝ) : qx (-φ) = toLeft2 (qx φ) := by
  simp only [qx, toLeft2_quat, neg_div, Real.cos_neg, Real.sin_neg, neg_zero]

lemma qz_neg_toLeft2 (θ : ℝ) : qz (-θ) = toLeft2 (qy θ) := by
  simp only [qy, qz, toLeft2_quat, neg_div, Real.cos_neg, Real.sin_neg, neg_zero]

def R2r : Matrix (Fin 3) (Fin 3) ℝ := Rz ψ * Rx φ * Ry θ
def R2l : Matrix (Fin 3) (Fin 3) ℝ := Ry (-ψ) * Rx (-φ) * Rz (-θ)
def q2r : Quaternion ℝ := qz ψ * qx φ * qy θ
def q2l : Quaternion ℝ := qy (-ψ) * qx (-φ) * qz (-θ)

theorem R2r_explicit : R2r θ φ ψ =
    !![cos ψ * cos θ - sin ψ * sin θ * sin φ, -(cos φ * sin ψ),
        cos ψ * sin θ + cos θ * sin ψ * sin φ;
      cos θ * sin ψ + cos ψ * sin θ * sin φ, cos ψ * cos φ,
        sin ψ * sin θ - cos ψ * cos θ * sin φ;
      -(cos φ * sin θ), sin φ, cos θ * cos φ] := by
  simp only [R2r, Ry, Rx, Rz]
  rw [Matrix.mul_fin_three, Matrix.mul_fin_three]
  apply m3_congr <;> ring1

theorem R2l_explicit : R2l θ φ ψ =
    !![cos ψ * cos θ - sin ψ * sin θ * sin φ, cos ψ * sin θ + cos θ * sin ψ * sin φ,
        -(cos φ * sin ψ);
      -(cos φ * sin θ), cos θ * cos φ, sin φ;
      cos θ * sin ψ + cos ψ * sin θ * sin φ, sin ψ * sin θ - cos ψ * cos θ * sin φ,
        cos ψ * cos φ] := by
  simp only [R2l, Ry, Rx, Rz, Real.cos_neg, Real.sin_neg]
  rw [Matrix.mul_fin_three, Matrix.mul_fin_three]
  apply m3_congr <;> ring1

theorem q2r_explicit : q2r θ φ ψ =
    quat (cos (ψ / 2) * cos (θ / 2) * cos (φ / 2) - sin (ψ / 2) * sin (θ / 2) * sin (φ / 2))
      (cos (ψ / 2) * cos (θ / 2) * sin (φ / 2) - cos (φ / 2) * sin (ψ / 2) * sin (θ / 2))
      (cos (ψ / 2) * cos (φ / 2) * sin (θ / 2) + cos (θ / 2) * sin (ψ / 2) * sin (φ / 2))
      (cos (θ / 2) * cos (φ / 2) * sin (ψ / 2) + cos (ψ / 2) * sin (θ / 2) * sin (φ / 2)) := by
  simp only [q2r, qx, qy, qz]
  rw [quat_mul, quat_mul]
  congr 1 <;> ring1

theorem q2l_eq_toLeft2 : q2l θ φ ψ = toLeft2 (q2r θ φ ψ) := by
  rw [q2l, q2r, toLeft2_mul, toLeft2_mul, qy_neg_toLeft2, qx_neg_toLeft2, qz_neg_toLeft2]

theorem q2l_explicit : q2l θ φ ψ =
    quat (cos (ψ / 2) * cos (θ / 2) * cos (φ / 2) - sin (ψ / 2) * sin (θ / 2) * sin (φ / 2))
      (cos (φ / 2) * sin (ψ / 2) * sin (θ / 2) - cos (ψ / 2) * cos (θ / 2) * sin (φ / 2))
      (-(cos (θ / 2) * cos (φ / 2) * sin (ψ / 2)) - cos (ψ / 2) * sin (θ / 2) * sin (φ / 2))
      (-(cos (ψ / 2) * cos (φ / 2) * sin (θ / 2)) - cos (θ / 2) * sin (ψ / 2) * sin (φ / 2)) := by
  rw [q2l_eq_toLeft2, q2r_explicit, toLeft2_quat]
  congr 1 <;> ring1

theorem nsq_q2r : nsq (q2r θ φ ψ) = 1 := by
  rw [q2r, nsq_mul, nsq_mul, nsq_qx, nsq_qy, nsq_qz]
  ring

theorem R2r_eq_rotmOf : R2r θ φ ψ = rotmOf (q2r θ φ ψ) := by
  rw [R2r, q2r, rotmOf_mul, rotmOf_mul, Rx_eq, Ry_eq, Rz_eq]

theorem R2l_eq_rotmOf : R2l θ φ ψ = rotmOf (q2l θ φ ψ) := by
  rw [R2l, q2l, rotmOf_mul, rotmOf_mul, Rx_eq, Ry_eq, Rz_eq]

/-- Swapping y and z: R_2l = P R_2r P. -/
theorem R2l_eq_P2_R2r_P2 : R2l θ φ ψ = P2 * R2r θ φ ψ * P2 := by
  rw [R2l_eq_rotmOf, R2r_eq_rotmOf, P2_rotmOf_P2, q2l_eq_toLeft2]

theorem rotm2quat_R2r (h : 0 < (q2r θ φ ψ).re) : rotm2quat (R2r θ φ ψ) = q2r θ φ ψ := by
  rw [R2r_eq_rotmOf]
  exact rotm2quat_rotmOf _ (nsq_q2r θ φ ψ) h

theorem rotm2quat_R2l (h : 0 < (q2r θ φ ψ).re) : rotm2quat (R2l θ φ ψ) = q2l θ φ ψ := by
  rw [R2l_eq_rotmOf]
  apply rotm2quat_rotmOf
  · rw [q2l_eq_toLeft2, nsq_toLeft2, nsq_q2r]
  · rw [q2l_eq_toLeft2]; exact h

/-- Rule of Example 2: q_l = (q_s, -q_x, -q_z, -q_y) of q_r, and back. -/
theorem rotm2quat_left2_eq_toLeft2 (h : 0 < (q2r θ φ ψ).re) :
    rotm2quat (R2l θ φ ψ) = toLeft2 (rotm2quat (R2r θ φ ψ)) := by
  rw [rotm2quat_R2l θ φ ψ h, rotm2quat_R2r θ φ ψ h, q2l_eq_toLeft2]

theorem rotm2quat_right2_eq_toLeft2 (h : 0 < (q2r θ φ ψ).re) :
    rotm2quat (R2r θ φ ψ) = toLeft2 (rotm2quat (R2l θ φ ψ)) := by
  rw [rotm2quat_left2_eq_toLeft2 θ φ ψ h, toLeft2_toLeft2]

/-- Position in Example 2: (x, y, z) ↦ (x, z, y). -/
theorem position_left2 (x y z : ℝ) : P2.mulVec ![x, y, z] = ![x, z, y] := by
  ext i
  fin_cases i <;> simp [P2, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

end Handedness
