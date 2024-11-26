/-

Authors: Giulio Caflisch, David Loeffler
-/
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.ContinuousMap.Compact

variable {G M : Type*} [AddCommMonoid M] [AddCommGroup G]
variable {S : Type*} [Semiring S] [Module S G]
variable {R : Type*} [Ring R] [Module R G]
variable {F : Type*} [Field F]

def fwdDiff (h : M) (f : M → G) : M → G :=
  fun x ↦ f (x + h) - f x

notation "δ_["h"]" => fwdDiff h

@[simp] theorem fwdDiff_const (h : M) (k : G) :
    δ_[h] (fun _ ↦ k) = (fun _ ↦ 0) := by
  ext x
  rw [fwdDiff]
  abel

@[simp] theorem fwdDiff_id (h : G) :
    δ_[h] id = (fun _ ↦ h) := by
  ext x
  simp_rw [fwdDiff, id_eq, add_sub_cancel_left]

@[simp] theorem fwdDiff_add (h : M) (f g : M → G) :
    δ_[h] (f + g) = δ_[h] f + δ_[h] g := by
  ext x
  simp only [Pi.add_apply, fwdDiff]
  abel

@[simp] theorem fwdDiff_sub (h : M) (f g : M → G) :
    δ_[h] (f - g) = δ_[h] f - δ_[h] g := by
  ext x
  simp only [Pi.sub_apply, fwdDiff]
  abel

@[simp] theorem fwdDiff_const_smul (h : M) (f : M → G) (r : S) :
    δ_[h] (r • f) = r • δ_[h] f := by
  ext x
  simp only [Pi.smul_apply, smul_sub, fwdDiff]

@[simp] theorem fwdDiff_finset_sum (h : M) {α : Type*} (s : Finset α) (f : α → M → G) :
    δ_[h] (∑ k ∈ s, f k) = ∑ k ∈ s, δ_[h] (f k) := by
  ext x
  simp only [Finset.sum_apply, Finset.sum_sub_distrib, fwdDiff]

@[simp] theorem fwdDiff_smul (h : M) (f : M → R) (g : M → G):
    δ_[h] (f • g) = δ_[h] f • g + f • δ_[h] g + δ_[h] f • δ_[h] g := by
  ext x
  simp only [Pi.add_apply, Pi.smul_apply', smul_sub, sub_smul, fwdDiff]
  abel

@[simp] theorem fwdDiff_div (h : M) (f g : M → F) (x : M) (hx : g x ≠ 0) (hx' : g (x + h) ≠ 0) :
    δ_[h] (f / g) x = ((δ_[h] f * g - f * δ_[h] g) / (g * (g + δ_[h] g))) x := by
  simp only [Pi.div_apply, Pi.sub_apply, Pi.mul_apply, Pi.add_apply, fwdDiff]
  rw [div_sub_div _ _ hx' hx, add_sub_cancel, div_eq_div_iff]
  ring
  · rw [mul_ne_zero_iff]
    constructor
    · exact hx'
    · exact hx
  · rw [mul_ne_zero_iff]
    constructor
    · exact hx
    · exact hx'

@[simp] theorem fwdDiff_zero_iterate (h : M) (n : ℕ) :
    δ_[h]^[n]  (fun (_ : M) ↦ (0 : G)) = (fun (_ : M) ↦ (0 : G)) := by
  induction' n with n hn
  · rw [Function.iterate_zero, id_eq]
  · rw [Function.iterate_succ_apply', hn, fwdDiff_const]

@[simp] theorem fwdDiff_iter_const_smul (h : M) (n : ℕ) (f : M → G) (r : S) :
    δ_[h]^[n] (r • f) = r • δ_[h]^[n] f := by
  revert f
  induction' n with n hn
  · simp_rw [Function.iterate_zero, id_eq, implies_true]
  · simp_rw [Function.iterate_succ, Function.comp_apply, fwdDiff_const_smul]
    intro f
    specialize hn (fwdDiff h f)
    exact hn

--------------------------------------------------------------------

theorem shift_eq_sum_fwdDiff_iter (h : M) (f : M → G) (n : ℕ) (y : M):
    f (y + n • h) = ∑ k ∈ Finset.range (n + 1), n.choose k • δ_[h]^[k] f y := by
  revert y
  induction' n with n hn
  · simp_rw [zero_smul, add_zero, zero_add, Finset.range_one, Finset.sum_singleton,
      Nat.choose_self, Function.iterate_zero, id_eq, one_smul, implies_true]
  · intro y
    have Hn := hn y
    rw [Finset.sum_range_succ'] at Hn
    rw [Finset.sum_range_succ', Nat.choose_zero_right]
    nth_rewrite 6 [← Nat.choose_zero_right n]
    simp_rw [Nat.choose_succ_succ, add_smul, one_smul, add_comm, ← add_assoc]
    rw [Finset.sum_add_distrib]
    nth_rewrite 2 [Finset.sum_range_succ]
    rw [Nat.choose_succ_self, zero_smul, add_zero]
    nth_rw 3 [add_comm]
    simp_rw [Nat.succ_eq_add_one]
    nth_rw 2 [add_assoc]
    nth_rw 3 [add_comm]
    simp_rw [← Hn, Function.iterate_succ_apply', fwdDiff, smul_sub, Finset.sum_sub_distrib, ← hn y,
      ← hn (y + h), add_sub_cancel]

theorem fwdDiff_iter_eq_sum_shift (h : M) (n : ℕ) (f : M → G) (x : M) :
    δ_[h]^[n] f x = ∑ k ∈ Finset.range (n + 1), ( (-(1 : ℤ))^(n - k) * (n.choose k) ) • f (x + k • h) := by
  revert x
  induction' n with n hn
  · simp_rw [Function.iterate_zero, id_eq, zero_add, Finset.sum_range_one, Nat.sub_zero, pow_zero,
      Nat.choose_zero_right, Nat.cast_one, mul_one, one_smul, zero_smul, add_zero, implies_true]
  · intro z
    rw [Function.iterate_succ_apply', fwdDiff, Finset.sum_range_succ', zero_smul, add_zero]
    simp only [Int.reduceNeg, Nat.reduceSubDiff, Nat.cast_add, Nat.cast_one, tsub_zero,
      Nat.choose_zero_right, mul_one, Nat.cast_zero, add_zero]
    simp_rw [Nat.choose_succ_succ', Nat.cast_add, mul_add, add_smul, Finset.sum_add_distrib]
    rw [hn, sub_eq_add_neg]
    simp_rw [one_smul, add_assoc, add_comm]
    rw [add_left_cancel_iff]
    nth_rewrite 1 [Finset.sum_range_succ]
    rw [Nat.choose_succ_self, Int.ofNat_zero, Int.mul_zero, zero_smul, add_zero]
    rw [hn, Finset.sum_range_succ', zero_smul, add_zero]
    simp only [Int.reduceNeg, Nat.cast_add, Nat.cast_one, tsub_zero, Nat.choose_zero_right, mul_one,
      Nat.cast_zero, add_zero, neg_add_rev]
    rw [Int.pow_succ']
    simp only [Int.reduceNeg, neg_mul, one_mul, neg_smul, add_right_inj]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← neg_smul, ← neg_one_mul, ← mul_assoc, ← Int.pow_succ']
    have : n - (x + 1) + 1 = n - x := by
      rw [Finset.mem_range] at hx
      omega
    rw [this, add_smul, one_smul]
    simp_rw [add_comm]

---------------------------------------------------------------------

theorem IsUltrametricDist.norm_fwdDiff_iter_apply_le {M G : Type*} [TopologicalSpace M] [CompactSpace M] [AddCommMonoid M] [SeminormedAddCommGroup G] [IsUltrametricDist G]
    (h : M) (f : C(M, G)) (m : M) (n : ℕ) : ‖δ_[h]^[n] f m‖ ≤ ‖f‖ := by
  rw [fwdDiff_iter_eq_sum_shift]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonempty
  · rw [Finset.nonempty_range_iff]
    apply Nat.add_one_ne_zero
  · intro i _
    calc
      _ ≤ ‖f (m + i • h)‖ := by
        apply IsUltrametricDist.norm_zsmul_le
      _ ≤ _ := by
        apply ContinuousMap.norm_coe_le_norm
