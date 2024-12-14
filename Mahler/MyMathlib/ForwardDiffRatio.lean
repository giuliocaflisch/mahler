/-

Authors: Giulio Caflisch, David Loeffler
-/

import Mahler.MyMathlib.ForwardDiff
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.RingTheory.Polynomial.Pochhammer

universe u
variable {R F : Type u} [CommRing R] [Field F] [Algebra R F] (h : R)

noncomputable def fwdDiffRatio (f : R → F) : R → F :=
  fun x ↦ (fwdDiff h f x) / (algebraMap R F h)

notation "Δ_["h"]" => fwdDiffRatio h
notation "Δ" => fwdDiffRatio 1

@[simp] theorem fwdDiffRatio_iter_fwdDiff (h : R) (f : R → F) (n : ℕ) :
    (fwdDiffRatio h)^[n] f = fun x ↦ ((fwdDiff h)^[n] f x) / (algebraMap R F h)^n := by
  induction' n with n hn
  · simp_rw [Function.iterate_zero, id_eq, pow_zero, div_one]
  · ext x
    simp_rw [Function.iterate_succ_apply']
    simp_rw [hn, fwdDiffRatio, fwdDiff, pow_succ, sub_div, div_div]

/-
theorem fwdDiff_descPochhammer (k : ℕ) : δ_[1] (fun x : R ↦ (descPochhammer R k).eval x) = fun x : R ↦ k • (descPochhammer R (k - 1)).eval x := by
  induction' k with k hk
  · simp_rw [descPochhammer_zero, Polynomial.eval_one, fwdDiff_const, zero_smul]
  · ext x
    simp_rw [descPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_comp,
      Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X, add_tsub_cancel_right]
    simp_rw [← Pi.mul_def, ← smul_eq_mul, fwdDiff_smul]
    simp_rw [smul_eq_mul, Pi.add_apply, Pi.mul_apply]
    simp_rw [fwdDiff_id', one_mul]
    calc
      _ = Polynomial.eval (x - 1) (descPochhammer R k) + x * δ_[1] ((fun i ↦ Polynomial.eval i (descPochhammer R k)) ∘ (fun i ↦ i - 1)) x := by
        sorry
      _ = Polynomial.eval (x - 1) (descPochhammer R k) + x * (δ_[1] (fun i ↦ Polynomial.eval i (descPochhammer R k)) ∘ (fun i ↦ i - 1)) x := by
        sorry
      _ = Polynomial.eval (x - 1) (descPochhammer R k) + x * δ_[1] (fun i ↦ Polynomial.eval i (descPochhammer R k)) (x - 1) := by
        rw [Function.comp_apply]
    simp_rw [hk]

    /-
    rw [fwdDiff, add_sub_right_comm, add_comm]
    -/
    --simp only [add_sub_cancel_right]
-/



/-
universe u

variable {D : Type*} [DivisionRing D]
variable {R : Subring D} (h : R)

noncomputable def fwdDiffRatio (f : R → D) : R → D :=
  fun x ↦ (fwdDiff h f x) / h

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
