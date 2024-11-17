/-
Dummy message for github commit

Authors: Giulio Caflisch, David Loeffler
-/

import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.ContinuousMap.Compact

/-!
# One dimensional forward difference operator

This file defines the forward difference operator of a function `f : M → G` where `M` is a
commutative monoid with one and `G` is a commutative group. The forward difference operator
of such a function `f` at a point `x` is given by an element `f' : G`.
-/

variable {G S M : Type*} [AddCommMonoidWithOne M] [AddCommGroup G] [Semiring S] [Module S G]
variable {R : Type*} [Ring R]
variable {F : Type*} [Field F]

/-- Forward difference operator, `fwddiff f n = f (n + 1) - f n`. -/
def fwddiff (f : M → G) : M → G :=
  fun x ↦ f (x + 1) - f x

@[simp] theorem fwddiff_const (k : G) :
    fwddiff (fun (_ : M) ↦ k) = (fun (_ : M) ↦ (0 : G)) := by
  ext y
  rw [fwddiff]
  abel

@[simp] theorem fwddiff_add (f g : M → G) :
    fwddiff (f + g) = fwddiff f + fwddiff g := by
  ext x
  simp only [Pi.add_apply]
  repeat rw [fwddiff]
  simp only [Pi.add_apply]
  abel

@[simp] theorem fwddiff_sub (f g : M → G) :
    fwddiff (f - g) = fwddiff f - fwddiff g := by
  ext x
  simp only [Pi.sub_apply]
  repeat rw [fwddiff]
  simp only [Pi.sub_apply]
  abel

@[simp] theorem fwddiff_const_smul (f : M → G) (r : S) :
    fwddiff (r • f) = r • fwddiff f := by
  ext x
  simp only [Pi.smul_apply]
  repeat rw [fwddiff]
  simp only [Pi.smul_apply]
  rw [smul_sub]

@[simp] lemma fwddiff_finset_sum {α : Type*} (s : Finset α) (f : α → M → G) :
    fwddiff (∑ k ∈ s, f k) = ∑ k ∈ s, fwddiff (f k) := by
  ext x
  simp only [Finset.sum_apply, fwddiff, Finset.sum_sub_distrib]

@[simp] theorem fwddiff_mul (f g : M → R) :
    fwddiff/-_[s]-/ (f * g) = fwddiff f * g + f * fwddiff g + /-s •-/ fwddiff f * fwddiff g := by
  ext x
  simp only [Pi.add_apply, Pi.mul_apply]
  repeat rw [fwddiff]
  simp only [Pi.mul_apply]
  repeat rw [mul_sub]
  repeat rw [sub_mul]
  abel

@[simp] theorem fwddiff_div (f g : M → F) (x : M) (hx : g x ≠ 0) (hx' : g (x + 1) ≠ 0) :
    fwddiff/-_[s]-/ (f / g) x = ((fwddiff f * g - f * fwddiff g) / (g * (g + /-s • -/ fwddiff g))) x := by
  simp only [Pi.div_apply, Pi.sub_apply, Pi.mul_apply, Pi.add_apply]
  repeat rw [fwddiff]
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

@[simp] theorem fwddiff_zero_iterate (n : ℕ) :
    fwddiff^[n] (fun (_ : M) ↦ (0 : G)) = (fun (_ : M) ↦ (0 : G)) := by
  induction' n with n hn
  · simp only [Function.iterate_zero, id_eq]
  · simp only [Function.iterate_succ_apply']
    rw [hn]
    rw [fwddiff_const]

--------------------------------------------------------------------

def extended_binomial_transform (n : ℕ) (x : ℕ) (a : ℕ → G) :=
  ∑ k ∈ Finset.range (n + 1), x.choose k • (a k)

def binomial_transform (n : ℕ) (a : ℕ → G) :=
  extended_binomial_transform n n a

def inverse_binomial_transform (n : ℕ) (s : ℕ → G) :=
  ∑ k ∈ Finset.range (n + 1), ( (-(1 : ℤ))^(n - k) * (n.choose k) ) • s k

--------------------------------------------------------------------

def newton_simple (f : M → G) (n : ℕ) (x : ℕ) :=
  ∑ k ∈ Finset.range (n + 1), x.choose k • fwddiff^[k] f

theorem newton_simple_of_eq (f : M → G) (n : ℕ) (y : M):
    newton_simple f n n y = f (y + n) := by
  rw [newton_simple, Finset.sum_apply]
  simp_rw [Pi.smul_apply]
  revert y
  induction' n with n hn
  · simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.choose_self, Function.iterate_zero, id_eq, one_smul, Nat.cast_zero, add_zero, implies_true]
  · intro z
    have Hn := hn z
    rw [Finset.sum_range_succ'] at Hn
    have Hn' := hn z
    have Hn'' := hn (z + 1)
    rw [Finset.sum_range_succ', Nat.choose_zero_right]
    nth_rewrite 5 [← Nat.choose_zero_right n]
    simp_rw [Nat.choose_succ_succ, add_smul]
    rw [Finset.sum_add_distrib]
    nth_rewrite 2 [Finset.sum_range_succ]
    rw [Nat.choose_succ_self, zero_smul, add_zero]
    rw [add_assoc]
    rw [Nat.cast_add]
    nth_rewrite 5 [← add_comm]
    nth_rewrite 2 [← add_assoc]
    rw [Hn]
    simp_rw [Function.iterate_succ_apply', fwddiff, smul_sub, Finset.sum_sub_distrib]
    rw [Hn', Hn'']
    simp only [sub_add_cancel, Nat.cast_one]

theorem newton_simple_of_le (f : M → G) (N n : ℕ) (y : M) (hn : n ≤ N) :
    newton_simple f N n y = f (y + n) := by
  rw [← Nat.add_sub_cancel' hn, newton_simple, add_right_comm, Finset.sum_range_add, ← newton_simple, Pi.add_apply, newton_simple_of_eq]
  have (x : ℕ) : n.choose (n + 1 + x) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  simp only [this, zero_smul, Finset.sum_const_zero, Pi.zero_apply, add_zero]

---------------------------------------------------------------------

@[simp] theorem fwddiff_iterate_const_smul (n : ℕ) (f : M → G) (r : S) :
    fwddiff^[n] (r • f) = r • fwddiff^[n] f := by
  revert f
  induction' n with n hn
  · simp only [Function.iterate_zero, id_eq, implies_true]
  · simp only [Function.iterate_succ, Function.comp_apply, fwddiff_const_smul]
    intro f
    specialize hn (fwddiff f)
    exact hn

theorem fwddiff_iterate (n : ℕ) (f : M → G) (x : M) :
    fwddiff^[n] f x = ∑ k ∈ Finset.range (n + 1), ( (-(1 : ℤ))^(n - k) * (n.choose k) ) • f (x + /-s •-/k) /-/ s^[n]-/ := by
  revert x
  induction' n with n hn
  · simp only [Function.iterate_zero, id_eq, zero_add, Finset.range_one, Int.reduceNeg, zero_le, tsub_eq_zero_of_le, pow_zero, one_mul, natCast_zsmul, Finset.sum_singleton, Nat.choose_self, Nat.cast_zero, add_zero, one_smul, implies_true]
  · intro z
    rw [Function.iterate_succ_apply', fwddiff, Finset.sum_range_succ']
    simp only [Int.reduceNeg, Nat.reduceSubDiff, Nat.cast_add, Nat.cast_one, tsub_zero, Nat.choose_zero_right, mul_one, Nat.cast_zero, add_zero]
    simp_rw [Nat.choose_succ_succ', Nat.cast_add, mul_add, add_smul, Finset.sum_add_distrib]
    rw [hn, sub_eq_add_neg]
    simp_rw [add_assoc, add_comm]
    rw [add_left_cancel_iff]
    nth_rewrite 1 [Finset.sum_range_succ]
    rw [Nat.choose_succ_self, Int.ofNat_zero, Int.mul_zero, zero_smul, add_zero]
    rw [hn, Finset.sum_range_succ']
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
    rw [this]

theorem fwddiff_iterate_at_zero_bounded_by_function_norm {X Y : Type*} [AddCommMonoidWithOne X] [TopologicalSpace X] [CompactSpace X] [NormedAddCommGroup Y] [IsUltrametricDist Y]
    (f : C(X, Y)) (x : X) (n : ℕ) : ‖fwddiff^[n] f x‖ ≤ ‖f‖ := by
  rw [fwddiff_iterate]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonempty
  · simp only [Finset.nonempty_range_iff, ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true]
  · intro i _
    calc
      _ ≤ ‖f (x + i)‖ := by
        apply IsUltrametricDist.norm_zsmul_le
      _ ≤ _ := by
        exact ContinuousMap.norm_coe_le_norm f (x + i)
