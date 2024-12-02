/-

Authors: Giulio Caflisch, David Loeffler
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.NumberTheory.Padics.MahlerBasis

--------------------------------------------------------------------------------------------------------------------------------

theorem ContinuousMap.exists_norm_eq_norm_apply
  {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X] [NormedAddCommGroup Y]
    (f : C(X, Y)) : ∃ x : X, ‖f x‖ = ‖f‖ := by
  obtain ⟨x, hx⟩ :=
    isCompact_univ.exists_sSup_image_eq Set.univ_nonempty (map_continuous f).norm.continuousOn
  use x
  rw [ContinuousMap.norm_eq_iSup_norm, ← And.right hx, Set.image_univ, sSup_range]

--------------------------------------------------------------------------------------------------------------------------------

theorem descPochhammer_eval_nat_eq_descFactorial (n k : ℕ) :
    (descPochhammer ℤ k).eval (Int.ofNat n) = n.descFactorial k := by
  induction' k with k hk
  · simp_rw [descPochhammer_zero, Polynomial.eval_one, Nat.descFactorial_zero, Nat.cast_one]
  · simp_rw [descPochhammer_succ_eval, hk, Int.ofNat_eq_coe, Nat.descFactorial_succ, Nat.cast_mul]
    by_cases h : n < k
    · rw [Nat.descFactorial_of_lt h, CharP.cast_eq_zero, zero_mul, mul_zero]
    · rw [not_lt] at h
      simp_rw [mul_comm, mul_eq_mul_right_iff, Int.ofNat_sub h, true_or]

--------------------------------------------------------------------------------------------------------------------------------

theorem WithTop.add_one_le_iff
  {α : Type*} [Preorder α] [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α] (x : α) (y : WithTop α) :
    x + 1 ≤ y ↔ x < y := by
  by_cases hy : y = ⊤
  · simp_rw [hy, WithTop.coe_lt_top, le_top]
  · obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp hy
    rw [← hz, WithTop.coe_lt_coe, ← WithTop.coe_one, ← WithTop.coe_add, WithTop.coe_le_coe]
    exact Order.add_one_le_iff

theorem WithTop.le_add_one
  {α : Type*} [AddZeroClass α] [Preorder α] [AddLeftMono α] [One α] [ZeroLEOneClass α] (x : α) :
    (x : WithTop α) ≤ (x + 1 : WithTop α) :=
  le_add_of_le_of_nonneg (le_refl _) zero_le_one

--------------------------------------------------------------------------------------------------------------------------------

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

@[simp] theorem Padic.addValuation_lt_addValuation (x : ℚ_[p]) (y : ℚ_[p]) :
    Padic.addValuation y < Padic.addValuation x ↔ ‖x‖ < ‖y‖ := by
  by_cases hx : x = 0
  · rw [hx]
    simp only [norm_zero, norm_pos_iff, _root_.AddValuation.map_zero]
    apply Iff.intro
    · intro hy
      by_contra!
      rw [this, _root_.AddValuation.map_zero, lt_self_iff_false] at hy
      exact hy
    · intro hy
      by_contra!
      simp_rw [top_le_iff, AddValuation.top_iff] at this
      exact hy this
  · rw [← ne_eq] at hx
    by_cases hy : y = 0
    · simp_rw [hy, _root_.AddValuation.map_zero, not_top_lt, norm_zero, false_iff, not_lt,
        norm_nonneg]
    · rw [← ne_eq] at hy
      simp_rw [Padic.norm_eq_pow_val hx, Padic.norm_eq_pow_val hy, Padic.addValuation.apply hx,
        Padic.addValuation.apply hy, ← Real.rpow_intCast,
        Real.rpow_lt_rpow_left_iff (Nat.one_lt_cast.mpr hp.out.one_lt),
        Int.cast_neg, neg_lt_neg_iff, Int.cast_lt, WithTop.coe_lt_coe]

@[simp] theorem Padic.addValuation_le_addValuation (x : ℚ_[p]) (y : ℚ_[p]) :
    Padic.addValuation y ≤ Padic.addValuation x ↔ ‖x‖ ≤ ‖y‖ := by
  by_cases hx : x = 0
  · simp_rw [hx, norm_zero, norm_nonneg, _root_.AddValuation.map_zero, le_top]
  · rw [← ne_eq] at hx
    by_cases hy : y = 0
    · rw [hy, norm_zero, norm_le_zero_iff, _root_.AddValuation.map_zero, top_le_iff,
        AddValuation.top_iff]
    · rw [← ne_eq] at hy
      simp_rw [Padic.norm_eq_pow_val hx, Padic.norm_eq_pow_val hy, Padic.addValuation.apply hx,
        Padic.addValuation.apply hy, ← Real.rpow_intCast,
        Real.rpow_le_rpow_left_iff (Nat.one_lt_cast.mpr hp.out.one_lt), Int.cast_neg,
        neg_le_neg_iff, Int.cast_le, WithTop.coe_le_coe]

@[simp] theorem Padic.lt_addValuation (x : ℚ_[p]) (m : ℤ) :
    m < Padic.addValuation x ↔ ‖x‖ < (p : ℝ)^(-m) := by
  by_cases hx : x = 0
  · simp_rw [hx, Padic.addValuation.map_zero, WithTop.coe_lt_top, norm_zero, zpow_neg, inv_pos,
      true_iff, ← Real.rpow_intCast]
    exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.out.pos) _
  · rw [← ne_eq] at hx
    simp_rw [Padic.norm_eq_pow_val hx, Padic.addValuation.apply hx, WithTop.coe_lt_coe,
      ← Real.rpow_intCast, Real.rpow_lt_rpow_left_iff (Nat.one_lt_cast.mpr hp.out.one_lt),
      Int.cast_neg, neg_lt_neg_iff, Int.cast_lt]

@[simp] theorem Padic.le_addValuation (x : ℚ_[p]) (m : ℤ) :
    m ≤ Padic.addValuation x ↔ ‖x‖ ≤ (p : ℝ)^(-m) := by
  by_cases hx : x = 0
  · simp_rw [hx, Padic.addValuation.map_zero]
    simp_rw [norm_zero, zpow_neg, inv_nonneg, le_top, true_iff, ← Real.rpow_intCast]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · rw [← ne_eq] at hx
    simp_rw [Padic.norm_eq_pow_val hx, Padic.addValuation.apply hx, WithTop.coe_le_coe,
      ← Real.rpow_intCast, Real.rpow_le_rpow_left_iff (Nat.one_lt_cast.mpr hp.out.one_lt),
      Int.cast_neg, neg_le_neg_iff, Int.cast_le]

@[simp] theorem Padic.addValuation_le (x : ℚ_[p]) (m : ℤ) :
    Padic.addValuation x ≤ m ↔ (p : ℝ)^(-m) ≤ ‖x‖ := by
  by_cases hx : x = 0
  · simp_rw [hx, Padic.addValuation.map_zero]
    simp only [norm_zero, zpow_neg, inv_nonneg, le_top, iff_true, top_le_iff, WithTop.coe_ne_top,
      inv_nonpos, false_iff, not_le, gt_iff_lt, ← Real.rpow_intCast]
    exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.out.pos) _
  · rw [← ne_eq] at hx
    simp_rw [Padic.norm_eq_pow_val hx, Padic.addValuation.apply hx, WithTop.coe_le_coe,
      ← Real.rpow_intCast, Real.rpow_le_rpow_left_iff (Nat.one_lt_cast.mpr hp.out.one_lt),
      Int.cast_neg, neg_le_neg_iff, Int.cast_le]

@[simp] theorem Padic.eq_addValuation_iff_norm_eq_pow_neg (x : ℚ_[p]) (m : ℤ) :
    m = Padic.addValuation x ↔ ‖x‖ = (p : ℝ)^(-m) := by
  simp only [le_antisymm_iff, Padic.le_addValuation, zpow_neg, Padic.addValuation_le]

--------------------------------------------------------------------------------------------------------------------------------

theorem PadicInt.norm_descPochhammer_le (k : ℕ) (x : ℤ_[p]) :
    ‖(descPochhammer ℤ_[p] k).eval x‖ ≤ ‖(k.factorial : ℚ_[p])‖ := by
  calc
    _ = ‖(-1)^k * (descPochhammer ℤ_[p] k).eval x‖ := by
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    _ = ‖(ascPochhammer ℤ_[p] k).eval (-x)‖ := by
      rw [← ascPochhammer_eval_neg_eq_descPochhammer]
    _ ≤ _ := norm_ascPochhammer_le _ _
