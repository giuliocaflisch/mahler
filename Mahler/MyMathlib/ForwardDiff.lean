import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Operations
import Mathlib.Algebra.Ring.Defs

import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Data.Nat.Choose.Sum

import Mathlib.Algebra.Module.Defs

import Mathlib.Tactic.Abel

variable {G M : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

def fwdDiff (f : M → G) : M → G :=
  fun x ↦ f (x + h) - f x

notation "δ_["h"]" => fwdDiff h

/-! Unapplied versions -/

@[simp] theorem fwdDiff_add (f g : M → G) :
    δ_[h] (f + g) = δ_[h] f + δ_[h] g := by
  ext x
  simp_rw [Pi.add_apply, fwdDiff, Pi.add_apply]
  abel

@[simp] theorem fwdDiff_const (k : G) :
    δ_[h] (fun _ ↦ k) = (fun _ ↦ 0) := by
  ext x
  rw [fwdDiff, sub_self]

@[simp] theorem fwdDiff_smul {R : Type*} [Ring R] [Module R G] (f : M → R) (g : M → G):
    δ_[h] (f • g) = δ_[h] f • g + f • δ_[h] g + δ_[h] f • δ_[h] g := by
  ext x
  simp only [fwdDiff, Pi.add_apply, Pi.smul_apply', sub_smul, smul_sub]
  abel

@[simp] theorem fwdDiff_const_smul {S : Type*} [Semiring S] [Module S G] (r : S) (f : M → G) :
    δ_[h] (r • f) = r • δ_[h] f := by
  ext x
  simp only [fwdDiff, Pi.smul_apply, smul_sub]

@[simp] theorem fwdDiff_finset_sum {α : Type*} (s : Finset α) (f : α → M → G) :
    δ_[h] (∑ k ∈ s, f k) = ∑ k ∈ s, δ_[h] (f k) := by
  ext x
  simp only [fwdDiff, Finset.sum_apply, Finset.sum_sub_distrib]

@[simp] theorem fwdDiff_iter_add (f g : M → G) (n : ℕ) :
    δ_[h]^[n] (f + g) = δ_[h]^[n] f + δ_[h]^[n] g := by
  induction' n with n hn
  · simp_rw [Function.iterate_zero_apply]
  · simp_rw [Function.iterate_succ_apply', hn, fwdDiff_add]

@[simp] theorem fwdDiff_iter_const_smul {S : Type*} [Semiring S] [Module S G] (r : S) (f : M → G) (n : ℕ) :
    δ_[h]^[n] (r • f) = r • δ_[h]^[n] f := by
  induction' n with n hn
  · simp_rw [Function.iterate_zero_apply]
  · simp_rw [Function.iterate_succ_apply', hn, fwdDiff_const_smul]

theorem fwdDiff_iter_eq_sum_shift (f : M → G) (n : ℕ) (x : M) :
    δ_[h]^[n] f x = ∑ k ∈ Finset.range (n + 1), ( (-1 : ℤ)^(n - k) * (n.choose k) ) • f (x + k • h) := by
  revert x
  induction' n with n hn
  · simp_rw [Function.iterate_zero_apply, zero_add, Finset.sum_range_one, Nat.sub_zero, pow_zero,
      Nat.choose_zero_right, Nat.cast_one, one_mul, one_smul, zero_smul, add_zero, implies_true]
  · intro x
    rw [Function.iterate_succ_apply', fwdDiff, Finset.sum_range_succ', zero_smul, add_zero,
      Nat.choose_zero_right, Nat.cast_one, mul_one, tsub_zero]
    simp_rw [add_tsub_add_eq_tsub_right, Nat.choose_succ_succ', Nat.cast_add, mul_add, add_smul,
      Finset.sum_add_distrib, one_smul, sub_eq_add_neg]
    rw [hn]
    simp_rw [add_assoc, add_comm, add_right_inj, Finset.sum_range_succ, Nat.choose_succ_self,
      Int.ofNat_zero, Int.mul_zero, zero_smul, add_zero, hn, Finset.sum_range_succ', zero_smul,
      add_zero, tsub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, neg_add_rev, Int.pow_succ',
      neg_one_mul, neg_smul, add_right_inj, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_range] at hx
    have : n - (x + 1) + 1 = n - x := by omega
    rw [← neg_smul, ← neg_one_mul, ← mul_assoc, ← Int.pow_succ', this, add_smul, one_smul]
    simp_rw [add_comm]

theorem shift_eq_sum_fwdDiff_iter (f : M → G) (n : ℕ) (y : M) :
    f (y + n • h) = ∑ k ∈ Finset.range (n + 1), n.choose k • δ_[h]^[k] f y := by
  revert y
  induction' n with n hn
  · simp_rw [zero_smul, add_zero, zero_add, Finset.sum_range_one, Nat.choose_self,
      one_smul,Function.iterate_zero_apply, implies_true]
  · intro y
    rw [Finset.sum_range_succ', Nat.choose_zero_right]
    nth_rw 6 [← Nat.choose_zero_right n]
    simp_rw [Nat.choose_succ_succ', add_smul, Finset.sum_add_distrib, one_smul, add_assoc]
    nth_rw 2 [Finset.sum_range_succ]
    simp_rw [Nat.choose_succ_self, zero_smul, add_zero,
      ← Finset.sum_range_succ' (fun x ↦ n.choose x • δ_[h]^[x] f y) _, ← hn y, Function.iterate_succ_apply',
      -- ← fwdDiff_const_smul_apply, ← fwdDiff_finset_sum_apply, ← funext hn]
      fwdDiff, smul_sub, Finset.sum_sub_distrib, ← hn, sub_add_cancel]
    simp only [add_comm, ← add_assoc]
