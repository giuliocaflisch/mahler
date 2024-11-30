/-

Authors: Giulio Caflisch, David Loeffler
-/

import Mahler.ForwardDiff

universe u

variable {D : Type*} [DivisionRing D]
variable {R : Subring D} (h : R)

noncomputable def fwdDiffRatio (f : R → D) : R → D :=
  fun x ↦ (fwdDiff h f x) / h

notation "Δ_["h"]" => fwdDiffRatio h

theorem fwdDiffRatio_iter_fwdDiff (h : R) (f : R → D) (n : ℕ) :
    (fwdDiffRatio h)^[n] f = fun x ↦ ((fwdDiff h)^[n] f x) / h^n := by
  induction' n with n hn
  · simp_rw [Function.iterate_zero, id_eq, pow_zero, div_one]
  · ext x
    simp_rw [Function.iterate_succ_apply']
    simp_rw [hn, fwdDiffRatio, fwdDiff, sub_div, ← div_mul_eq_div_div_swap, pow_succ']

theorem fwdDiffRatio_eq_fwdDiff_step_one :
    fwdDiffRatio (1 : R) = fwdDiff (1 : R) := by
  ext f x
  rw [fwdDiffRatio, OneMemClass.coe_one, div_one]

------------------------------------------------------------------------

/-
universe u
variable {R F : Type u} [CommRing R] [Field F] [Algebra R F]

noncomputable def fwdDiffRatio (h : R) (f : R → F) : R → F :=
  fun x ↦ (fwdDiff h f x) / (algebraMap R F h)

@[simp] theorem fwdDiffRatio_iter_fwdDiff (h : R) (f : R → F) (n : ℕ) :
    (fwdDiffRatio h)^[n] f = fun x ↦ ((fwdDiff h)^[n] f x) / (algebraMap R F h)^n := by
  induction' n with n hn
  · simp_rw [Function.iterate_zero, id_eq, pow_zero, div_one]
  · ext x
    simp_rw [Function.iterate_succ_apply']
    simp_rw [hn, fwdDiffRatio, fwdDiff, pow_succ, sub_div, div_div]

-/

------------------------------------------------------------------------

/-

variable {R : Type*} [Ring R]
variable {M : Subring R} (h : M) [H : Fact (IsUnit (h : R))]

noncomputable def discDeriv (f : M → R) : M → R :=
  fun x ↦ (fwdDiff h f x) * (H.out.unit.inv : R)

@[simp] theorem discDeriv_iter_fwdDiff (f : M → R) (n : ℕ) :
    (discDeriv h)^[n] f = fun x ↦ ((fwdDiff h)^[n] f x) * (H.out.unit.inv : R)^n := by
  induction' n with n hn
  · simp_rw [Function.iterate_zero_apply, pow_zero, mul_one]
  · ext x
    simp_rw [Function.iterate_succ_apply', hn, discDeriv, fwdDiff, sub_mul, mul_assoc, ← pow_succ]
-/
