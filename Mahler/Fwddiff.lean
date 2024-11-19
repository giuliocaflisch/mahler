/-

Authors: Giulio Caflisch, David Loeffler
-/

import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.ContinuousMap.Compact

variable {G S M : Type*} [AddCommMonoid M] [AddCommGroup G] [Semiring S] [Module S G]
variable {R : Type*} [Ring R]
variable {F : Type*} [Field F]
variable {H : AddSubmonoid F}

def fwdDiff (h : M) (f : M -> G) : M -> G :=
  fun x => f (x + h) - f x

def discDeriv (h : H) (f : H -> F) : H -> F :=
  fun x => fwdDiff h f x / h

@[simp] theorem fwdDiff_const (h : M) (k : G) :
    fwdDiff h (fun (_ : M) => k) = (fun (_ : M) => (0 : G)) := by
  ext y
  rw [fwdDiff]
  abel

@[simp] theorem fwdDiff_add (h : M) (f g : M -> G) :
    fwdDiff h (f + g) = fwdDiff h f + fwdDiff h g := by
  ext x
  simp only [Pi.add_apply]
  repeat rw [fwdDiff]
  simp only [Pi.add_apply]
  abel

@[simp] theorem fwdDiff_sub (h : M) (f g : M -> G) :
    fwdDiff h (f - g) = fwdDiff h f - fwdDiff h g := by
  ext x
  simp only [Pi.sub_apply]
  repeat rw [fwdDiff]
  simp only [Pi.sub_apply]
  abel

@[simp] theorem fwdDiff_const_smul (h : M) (f : M -> G) (r : S) :
    fwdDiff h (r • f) = r • fwdDiff h f := by
  ext x
  simp only [Pi.smul_apply]
  repeat rw [fwdDiff]
  simp only [Pi.smul_apply]
  rw [smul_sub]

@[simp] lemma fwdDiff_finset_sum (h : M) {α : Type*} (s : Finset α) (f : α -> M -> G) :
    fwdDiff h (∑ k ∈ s, f k) = ∑ k ∈ s, fwdDiff h (f k) := by
  ext x
  simp only [Finset.sum_apply, fwdDiff, Finset.sum_sub_distrib]

@[simp] theorem fwdDiff_mul (h : M) (f g : M -> R) :
    fwdDiff h (f * g) = fwdDiff h f * g + f * fwdDiff h g + fwdDiff h f * fwdDiff h g := by
  ext x
  simp only [Pi.add_apply, Pi.mul_apply]
  repeat rw [fwdDiff]
  simp only [Pi.mul_apply]
  repeat rw [mul_sub]
  repeat rw [sub_mul]
  abel

@[simp] theorem fwdDiff_div (h : M) (f g : M -> F) (x : M) (hx : g x ≠ 0) (hx' : g (x + h) ≠ 0) :
    fwdDiff h (f / g) x = ((fwdDiff h f * g - f * fwdDiff h g) / (g * (g + fwdDiff h g))) x := by
  simp only [Pi.div_apply, Pi.sub_apply, Pi.mul_apply, Pi.add_apply]
  repeat rw [fwdDiff]
  simp only [Pi.div_apply]
  rw [div_sub_div]
  simp only [add_sub_cancel]
  rw [div_eq_div_iff]
  ring
  rw [mul_ne_zero_iff]
  · constructor
    · exact hx'
    · exact hx
  · rw [mul_ne_zero_iff]
    constructor
    · exact hx
    · exact hx'
  · exact hx'
  · exact hx

@[simp] theorem fwdDiff_zero_iterate (h : M) (n : ℕ) :
    (fwdDiff h)^[n]  (fun (_ : M) => (0 : G)) = (fun (_ : M) => (0 : G)) := by
  induction' n with n hn
  · simp only [Function.iterate_zero, id_eq]
  · simp only [Function.iterate_succ_apply']
    rw [hn]
    rw [fwdDiff_const]

--------------------------------------------------------------------

theorem shift_eq_sum_fwdDiff_iter (h : M) (f : M -> G) (n : ℕ) (y : M):
    f (y + n • h) = ∑ k ∈ Finset.range (n + 1), n.choose k • (fwdDiff h)^[k] f y := by
  revert y
  induction' n with n hn
  · simp only [zero_smul, add_zero, zero_add, Finset.range_one, Finset.sum_singleton, Nat.choose_self, Function.iterate_zero, id_eq, one_smul, implies_true]
  · intro z
    have Hn := hn z
    rw [Finset.sum_range_succ'] at Hn
    have Hn' := hn z
    have Hn'' := hn (z + h)
    rw [Finset.sum_range_succ', Nat.choose_zero_right]
    nth_rewrite 6 [← Nat.choose_zero_right n]
    simp_rw [Nat.choose_succ_succ, add_smul, one_smul, add_comm, ← add_assoc]
    rw [Finset.sum_add_distrib]
    nth_rewrite 2 [Finset.sum_range_succ]
    rw [Nat.choose_succ_self, zero_smul, add_zero]
    nth_rw 3 [add_comm]
    simp only [Nat.succ_eq_add_one]
    nth_rw 2 [add_assoc]
    nth_rw 3 [add_comm]
    rw [← Hn]
    simp_rw [Function.iterate_succ_apply', fwdDiff, smul_sub, Finset.sum_sub_distrib]
    rw [← Hn', ← Hn'']
    simp only [add_sub_cancel]

---------------------------------------------------------------------

@[simp] theorem fwdDiff_iter_const_smul (h : M) (n : ℕ) (f : M -> G) (r : S) :
    (fwdDiff h)^[n] (r • f) = r • (fwdDiff h)^[n] f := by
  revert f
  induction' n with n hn
  · simp only [Function.iterate_zero, id_eq, implies_true]
  · simp only [Function.iterate_succ, Function.comp_apply, fwdDiff_const_smul]
    intro f
    specialize hn (fwdDiff h f)
    exact hn

theorem fwdDiff_iter_eq_sum_shift (h : M) (n : ℕ) (f : M -> G) (x : M) :
    (fwdDiff h)^[n] f x = ∑ k ∈ Finset.range (n + 1), ( (-(1 : ℤ))^(n - k) * (n.choose k) ) • f (x + k • h) := by
  revert x
  induction' n with n hn
  · simp only [Function.iterate_zero, id_eq, zero_add, Finset.range_one, Int.reduceNeg, zero_le, Nat.sub_eq_zero_of_le, pow_zero, one_mul, natCast_zsmul, Finset.sum_singleton, Nat.choose_self, zero_smul, add_zero, one_smul, implies_true]
  · intro z
    rw [Function.iterate_succ_apply', fwdDiff, Finset.sum_range_succ', zero_smul, add_zero]
    simp only [Int.reduceNeg, Nat.reduceSubDiff, Nat.cast_add, Nat.cast_one, tsub_zero, Nat.choose_zero_right, mul_one, Nat.cast_zero, add_zero]
    simp_rw [Nat.choose_succ_succ', Nat.cast_add, mul_add, add_smul, Finset.sum_add_distrib]
    rw [hn, sub_eq_add_neg]
    simp only [one_smul]
    simp_rw [add_assoc, add_comm]
    rw [add_left_cancel_iff]
    nth_rewrite 1 [Finset.sum_range_succ]
    rw [Nat.choose_succ_self, Int.ofNat_zero, Int.mul_zero, zero_smul, add_zero]
    rw [hn, Finset.sum_range_succ', zero_smul, add_zero]
    simp only [Int.reduceNeg, Nat.cast_add, Nat.cast_one, tsub_zero, Nat.choose_zero_right, mul_one, Nat.cast_zero, add_zero, neg_add_rev]
    rw [Int.pow_succ']
    simp only [Int.reduceNeg, neg_mul, one_mul, neg_smul, add_right_inj]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intros x hx
    rw [← neg_smul, ← neg_one_mul, ← mul_assoc, ← Int.pow_succ']
    have : n - (x + 1) + 1 = n - x := by -- this theorem doesn't hold for all natural numbers N and m due to saturation of -
      rw [Finset.mem_range] at hx
      omega
    rw [this, add_smul, one_smul]
    simp_rw [add_comm]

theorem fwdDiff_iter_bounded_by_function_norm {X Y : Type*} [AddCommMonoidWithOne X] [TopologicalSpace X] [CompactSpace X] [NormedAddCommGroup Y] [IsUltrametricDist Y]
    (h : X) (f : C(X, Y)) (x : X) (n : ℕ) : ‖(fwdDiff h)^[n] f x‖ ≤ ‖f‖ := by
  rw [fwdDiff_iter_eq_sum_shift]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonempty
  · simp only [Finset.nonempty_range_iff, ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true]
  · intro i _
    calc
      _ ≤ ‖f (x + i • h)‖ := by
        apply IsUltrametricDist.norm_zsmul_le
      _ ≤ _ := by
        exact ContinuousMap.norm_coe_le_norm f (x + i • h)
