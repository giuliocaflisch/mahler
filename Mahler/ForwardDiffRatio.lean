/-

Authors: Giulio Caflisch, David Loeffler
-/

import Mahler.ForwardDiff

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

------------------------------------------------------------------------

variable {P : Type*} [Ring P]
variable {M : AddSubmonoid P}

noncomputable def discDeriv (h : M) [H : Fact (IsUnit (h : P))] (f : M → P) : M → P :=
  fun x ↦ (fwdDiff h f x) * (H.out.unit.inv : P)

@[simp] theorem discDeriv_iter_fwdDiff (h : M) [H : Fact (IsUnit (h : P))] (f : M → P) (n : ℕ) :
    (discDeriv h)^[n] f = fun x ↦ ((fwdDiff h)^[n] f x) * (H.out.unit.inv : P)^n := by
  induction' n with n hn
  · simp_rw [Function.iterate_zero_apply, pow_zero, mul_one]
  · ext x
    simp_rw [Function.iterate_succ_apply', hn, discDeriv, fwdDiff, sub_mul, mul_assoc, ← pow_succ]
