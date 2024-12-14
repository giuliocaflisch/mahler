/-

Authors: Giulio Caflisch, David Loeffler
-/
import Mathlib.Algebra.Group.ForwardDiff

variable {G M : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

notation "δ_["h"]" => fwdDiff h

/-! This should be generalized for `M` submonoid of `G` and the inclusion map -/
@[simp] theorem fwdDiff_id (h : G) :
    δ_[h] id = (fun _ ↦ h) := by
  ext x
  simp_rw [fwdDiff, id_eq, add_sub_cancel_left]

@[simp] theorem fwdDiff_id' (h : G) :
    δ_[h] (fun x ↦ x) = (fun _ ↦ h) := by
  ext x
  simp_rw [fwdDiff, add_sub_cancel_left]

@[simp] theorem fwdDiff_sub (f g : M → G) :
    δ_[h] (f - g) = δ_[h] f - δ_[h] g := by
  ext x
  simp only [fwdDiff, Pi.sub_apply]
  abel

@[simp] theorem fwdDiff_div_apply {F : Type*} [Field F] (f g : M → F) (x : M) (hx : g x ≠ 0) (hx' : g (x + h) ≠ 0) :
    δ_[h] (f / g) x = ((δ_[h] f * g - f * δ_[h] g) / (g * (g + δ_[h] g))) x := by
  simp only [fwdDiff,Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, add_sub_cancel,
    div_sub_div _ _ hx' hx, div_eq_div_iff (mul_ne_zero hx' hx) (mul_ne_zero hx hx')]
  ring

@[simp] theorem fwdDiff_iter_const_zero (n : ℕ) :
    δ_[h]^[n]  (fun (_ : M) ↦ (0 : G)) = (fun (_ : M) ↦ (0 : G)) := by
  induction' n with n hn
  · rw [Function.iterate_zero_apply]
  · rw [Function.iterate_succ_apply', hn, fwdDiff_const]

/-! Applied that were needed originally -/

@[simp] theorem fwdDiff_const_smul_apply {S : Type*} [Semiring S] [Module S G] (r : S) (f : M → G) (x : M) :
    δ_[h] (r • f) x = r • δ_[h] f x := by
  rw [fwdDiff_const_smul, Pi.smul_apply]

@[simp] theorem fwdDiff_finset_sum_apply {α : Type*} (s : Finset α) (f : α → M → G) (x : M) :
    δ_[h] (∑ k ∈ s, f k) x = ∑ k ∈ s, δ_[h] (f k) x := by
  rw [fwdDiff_finset_sum, Finset.sum_apply]
