/-

Authors: Giulio Caflisch, David Loeffler
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.ContinuousMap.Compact

--------------------------------------------------------------------------------------------------------------------------------

theorem ContinuousMap.exists_norm_eq_norm_apply {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X] [NormedAddCommGroup Y]
    (f : C(X, Y)) : ∃ x : X, ‖f x‖ = ‖f‖ := by
  obtain ⟨x, hx⟩ := isCompact_univ.exists_sSup_image_eq Set.univ_nonempty (map_continuous f).norm.continuousOn
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
      rw [mul_comm, mul_eq_mul_right_iff, Int.ofNat_sub h, eq_self, true_or]
      trivial

--------------------------------------------------------------------------------------------------------------------------------

theorem WithTop.add_one_le_iff {α : Type*} [Preorder α] [Add α] [One α] [SuccAddOrder α] [NoMaxOrder α] (x : α) (y : WithTop α) : x + 1 ≤ y ↔ x < y := by
  by_cases hy : y = ⊤
  · simp_rw [hy, WithTop.coe_lt_top, le_top]
  · obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp hy
    rw [← hz, WithTop.coe_lt_coe, ← WithTop.coe_one, ← WithTop.coe_add, WithTop.coe_le_coe]
    apply Order.add_one_le_iff

theorem WithTopInt.add_one_le_iff' (x : ℕ) (y : WithTop ℤ) : x + 1 ≤ y ↔ x < y :=
  WithTop.add_one_le_iff _ _

theorem WithTop.le_add_one {α : Type*} [AddZeroClass (WithTop α)] [Preorder (WithTop α)] [AddLeftMono (WithTop α)] [One (WithTop α)] [ZeroLEOneClass (WithTop α)] (x : α) :
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
      by_contra! hy'
      simp_rw [hy', _root_.AddValuation.map_zero, lt_self_iff_false] at hy
    · intro hy
      by_contra hy'
      simp_rw [not_lt, top_le_iff, AddValuation.top_iff] at hy'
      exact hy hy'
  · rw [← ne_eq] at hx
    by_cases hy : y = 0
    · simp_rw [hy, _root_.AddValuation.map_zero, not_top_lt, norm_zero, false_iff, not_lt, norm_nonneg]
    · rw [← ne_eq] at hy
      simp_rw [Padic.norm_eq_pow_val hx, Padic.norm_eq_pow_val hy, Padic.addValuation.apply hx, Padic.addValuation.apply hy, ← Real.rpow_intCast, Real.rpow_lt_rpow_left_iff (Nat.one_lt_cast.mpr hp.out.one_lt), Int.cast_neg, neg_lt_neg_iff, Int.cast_lt, WithTop.coe_lt_coe]

@[simp] theorem Padic.addValuation_le_addValuation (x : ℚ_[p]) (y : ℚ_[p]) :
    Padic.addValuation y ≤ Padic.addValuation x ↔ ‖x‖ ≤ ‖y‖ := by
  by_cases hx : x = 0
  · simp_rw [hx, norm_zero, norm_nonneg, _root_.AddValuation.map_zero, le_top]
  · rw [← ne_eq] at hx
    by_cases hy : y = 0
    · rw [hy, norm_zero, norm_le_zero_iff, _root_.AddValuation.map_zero, top_le_iff, AddValuation.top_iff]
    · rw [← ne_eq] at hy
      simp_rw [Padic.norm_eq_pow_val hx, Padic.norm_eq_pow_val hy, Padic.addValuation.apply hx, Padic.addValuation.apply hy, ← Real.rpow_intCast, Real.rpow_le_rpow_left_iff (Nat.one_lt_cast.mpr hp.out.one_lt), Int.cast_neg, neg_le_neg_iff, Int.cast_le, WithTop.coe_le_coe]

@[simp] theorem Padic.lt_addValuation (x : ℚ_[p]) (m : ℤ) :
    m < Padic.addValuation x ↔ ‖x‖ < (p : ℝ)^(-m) := by
  by_cases hx : x = 0
  · simp_rw [hx, Padic.addValuation.map_zero, WithTop.coe_lt_top, norm_zero, zpow_neg, inv_pos, true_iff]
    have : 0 < (p : ℝ)^(m : ℝ) := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.out.pos) _
    rw [Real.rpow_intCast] at this
    exact this
  · rw [← ne_eq] at hx
    simp_rw [Padic.norm_eq_pow_val hx, Padic.addValuation.apply hx, WithTop.coe_lt_coe, ← Real.rpow_intCast, Real.rpow_lt_rpow_left_iff (Nat.one_lt_cast.mpr hp.out.one_lt), Int.cast_neg, neg_lt_neg_iff, Int.cast_lt]

@[simp] theorem Padic.lt_addValuation' (x : ℚ_[p]) (m : ℕ) :
    m < Padic.addValuation x ↔ ‖x‖ < (p : ℝ)^(-(m : ℤ)) := Padic.lt_addValuation _ _

@[simp] theorem Padic.le_addValuation (x : ℚ_[p]) (m : ℤ) :
    m ≤ Padic.addValuation x ↔ ‖x‖ ≤ (p : ℝ)^(-m) := by
  by_cases hx : x = 0
  · simp_rw [hx, Padic.addValuation.map_zero]
    simp only [norm_zero, zpow_neg, inv_nonneg, le_top, iff_true]
    have h : 0 ≤ (p : ℝ)^(m : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    rw [Real.rpow_intCast] at h
    simp_rw [true_iff, ge_iff_le]
    exact h
  · rw [← ne_eq] at hx
    simp_rw [Padic.norm_eq_pow_val hx, Padic.addValuation.apply hx, WithTop.coe_le_coe, ← Real.rpow_intCast]
    rw [Real.rpow_le_rpow_left_iff]
    simp_rw [Int.cast_neg, neg_le_neg_iff, Int.cast_le]
    · rw [Nat.one_lt_cast]
      exact hp.out.one_lt

@[simp] theorem Padic.addValuation_le (x : ℚ_[p]) (m : ℤ) :
    Padic.addValuation x ≤ m ↔ (p : ℝ)^(-m) ≤ ‖x‖ := by
  by_cases hx : x = 0
  · simp_rw [hx, Padic.addValuation.map_zero]
    simp only [norm_zero, zpow_neg, inv_nonneg, le_top, iff_true, top_le_iff, WithTop.coe_ne_top, inv_nonpos, false_iff, not_le, gt_iff_lt]
    have : 0 < (p : ℝ)^(m : ℝ) := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.out.pos) _
    simp only [Real.rpow_intCast] at this
    exact this
  · rw [← ne_eq] at hx
    simp_rw [Padic.norm_eq_pow_val hx, Padic.addValuation.apply hx, WithTop.coe_le_coe]
    simp_rw [← Real.rpow_intCast]
    rw [Real.rpow_le_rpow_left_iff]
    simp_rw [Int.cast_neg, neg_le_neg_iff]
    rw [Int.cast_le]
    · simp only [Nat.one_lt_cast]
      exact hp.out.one_lt

@[simp] theorem Padic.eq_addValuation_iff_norm_eq_pow_neg (x : ℚ_[p]) (m : ℤ) :
    m = Padic.addValuation x ↔ ‖x‖ = (p : ℝ)^(-m) := by
  repeat rw [le_antisymm_iff]
  simp only [Padic.le_addValuation, zpow_neg, Padic.addValuation_le]

@[simp] theorem Padic.le_addValuation_iff_norm_le_pow_neg' (x : ℚ_[p]) (m : ℕ) :
    m ≤ Padic.addValuation x ↔ ‖x‖ ≤ (p : ℝ)^(-(m : ℤ)) := Padic.le_addValuation _ _

--------------------------------------------------------------------------------------------------


theorem Padic.tendsto_atTop_norm_lt_pow (s : ℕ → ℚ_[p]) (L : ℚ_[p]):
    (Filter.Tendsto s Filter.atTop (nhds L)) ↔ ∀ m : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ‖s n - L‖ < (p : ℝ)^(-(m : ℤ)) := by
  simp only [Metric.tendsto_atTop, dist_eq_norm_sub]
  apply Iff.intro
  · intro Hε m
    specialize Hε ((p : ℝ)^(-(m : ℤ)))
    apply Hε
    apply zpow_pos
    exact Nat.cast_pos.mpr hp.out.pos
  · intro Hm ε hε
    obtain ⟨n, hn⟩ := by
      exact PadicInt.exists_pow_neg_lt p hε
    obtain ⟨u, hu⟩ := Hm n
    exact ⟨u, fun m hm ↦ (hu m hm).trans hn⟩

theorem Padic.tendsto_atTop_addValuation_lt (s : ℕ → ℚ_[p]) (L : ℚ_[p]):
    (Filter.Tendsto s Filter.atTop (nhds L)) ↔ ∀ m : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → m < Padic.addValuation (s n - L) := by
  simp_rw [Padic.tendsto_atTop_norm_lt_pow, Padic.lt_addValuation']

theorem Padic.tendsto_atTop_addValuation_le (s : ℕ → ℚ_[p]) (L : ℚ_[p]):
    (Filter.Tendsto s Filter.atTop (nhds L)) ↔ ∀ m : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → m ≤ Padic.addValuation (s n - L) := by
  rw [Padic.tendsto_atTop_addValuation_lt]
  apply Iff.intro
  · intro hlt m
    specialize hlt m
    obtain ⟨N, hN⟩ := hlt
    use N
    intro n hn
    apply le_of_lt
    apply hN
    exact hn
  · intro hle m
    specialize hle (m + 1)
    simp_rw [Nat.cast_add_one, WithTopInt.add_one_le_iff'] at hle
    exact hle

theorem Padic.tendsto_atTop_norm_le_pow (s : ℕ → ℚ_[p]) (L : ℚ_[p]):
    (Filter.Tendsto s Filter.atTop (nhds L)) ↔ ∀ m : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ‖s n - L‖ ≤ (p : ℝ)^(-(m : ℤ)) := by
  simp_rw [Padic.tendsto_atTop_addValuation_le, Padic.le_addValuation_iff_norm_le_pow_neg']

----------------------------------------------------------------------------------------

theorem Padic.uniformContinuous_iff_norm_lt_pow (f : ℤ_[p] → ℚ_[p]) :
    UniformContinuous f ↔ ∀ s : ℕ, ∃ t : ℕ, ∀ b a : ℤ_[p], ‖a - b‖ < p^(-(t : ℤ)) → ‖f a - f b‖ < p^(-(s : ℤ)) := by
  simp only [Metric.uniformContinuous_iff, dist_eq_norm_sub]
  apply Iff.intro
  · intro Hε s
    specialize Hε ((p : ℝ)^(-(s : ℤ)))
    obtain ⟨δ, hδ, Hδ⟩ := by
      apply Hε _
      apply (zpow_pos _)
      exact Nat.cast_pos.mpr hp.out.pos
    obtain ⟨t, ht⟩ := PadicInt.exists_pow_neg_lt p hδ
    use t
    intro b a ha
    exact Hδ (lt_of_lt_of_le ha (le_of_lt ht))
  · intro Hs ε hε
    obtain ⟨s, hs⟩ := PadicInt.exists_pow_neg_lt p hε
    specialize Hs s
    obtain ⟨t, ht⟩ := Hs
    use ((p : ℝ)^(-(t : ℤ)))
    apply And.intro (zpow_pos (Nat.cast_pos.mpr hp.out.pos) _)
    intro _ _ ha
    exact lt_of_lt_of_le (ht _ _ ha) (le_of_lt hs)

theorem Padic.uniformContinuous_iff_addValuation_lt (f : ℤ_[p] → ℚ_[p]) :
    UniformContinuous f ↔ ∀ s : ℕ, ∃ t : ℕ, ∀ b a : ℤ_[p], t < Padic.addValuation (a - b : ℚ_[p]) → s < Padic.addValuation (f a - f b) := by
  simp_rw [Padic.uniformContinuous_iff_norm_lt_pow, ← PadicInt.padic_norm_e_of_padicInt, Padic.lt_addValuation', PadicInt.coe_sub]

theorem Padic.uniformContinuous_iff_addValuation_le (f : ℤ_[p] → ℚ_[p]) :
    UniformContinuous f ↔ ∀ s : ℕ, ∃ t : ℕ, ∀ b a : ℤ_[p], t ≤ Padic.addValuation (a - b : ℚ_[p]) → s ≤ Padic.addValuation (f a - f b) := by
  rw [Padic.uniformContinuous_iff_addValuation_lt]
  apply Iff.intro
  · intro hlt s
    specialize hlt s
    obtain ⟨t, ht⟩ := hlt
    use (t + 1)
    intro a b h
    rw [Nat.cast_add_one, WithTopInt.add_one_le_iff'] at h
    apply le_of_lt
    apply ht
    exact h
  · intro hle s
    specialize hle (s + 1)
    obtain ⟨t, ht⟩ := hle
    simp_rw [Nat.cast_add_one, WithTopInt.add_one_le_iff'] at ht
    use t
    intro a b h
    apply ht
    apply le_of_lt
    exact h

theorem Padic.uniformContinuous_then_nonzero_addValuation_le (f : ℤ_[p] → ℚ_[p]) :
    UniformContinuous f → ∀ s : ℕ, ∃ t : ℕ, t ≠ 0 ∧ ∀ b a : ℤ_[p], t ≤ Padic.addValuation (a - b : ℚ_[p]) → s ≤ Padic.addValuation (f a - f b) := by
  rw [Padic.uniformContinuous_iff_addValuation_le]
  intro H0
  intro s
  specialize H0 s
  obtain ⟨t, ht⟩ := H0
  use t + 1
  apply And.intro
  · simp only [ne_eq, self_eq_add_left, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true]
  · intro b a ht'
    specialize ht b a
    apply ht
    calc
      (t : WithTop ℤ) ≤ ((t + 1) : WithTop ℤ) := WithTop.le_add_one _
      _ ≤ addValuation ((a : ℚ_[p]) - (b : ℚ_[p])) := ht'


theorem Padic.uniformContinuous_then_nonzero_norm_le_pow {f : ℤ_[p] → ℚ_[p]} :
    UniformContinuous f → ∀ s : ℕ, ∃ t : ℕ, t ≠ 0 ∧ ∀ b a : ℤ_[p], ‖a - b‖ ≤ p^(-(t : ℤ)) → ‖f a - f b‖ ≤ p^(-(s : ℤ)) := by
  intro hf
  /-
  -/
  have h := Padic.uniformContinuous_then_nonzero_addValuation_le f hf
  simp_rw [Padic.le_addValuation_iff_norm_le_pow_neg'] at h
  exact h
