/-

Authors: Giulio Caflisch, David Loeffler
-/
import Mahler.ForwardDiff
import Mahler.ForwardDiffRatio
import Mahler.Help
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Analysis.NormedSpace.FunctionSeries
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

private theorem Padic.tendsto_atTop_norm_le_pow (s : ℕ → ℚ_[p]) (L : ℚ_[p]) :
    (Filter.Tendsto s Filter.atTop (nhds L)) ↔ ∀ m : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ‖s n - L‖ ≤ (p : ℝ)^(-m : ℤ) := by
  simp_rw [Metric.tendsto_atTop, dist_eq_norm_sub]
  apply Iff.intro
  · intro Hε m
    specialize Hε ((p : ℝ)^(-m -1 : ℤ)) (zpow_pos (Nat.cast_pos.mpr hp.out.pos) _)
    obtain ⟨N, hN⟩ := Hε
    use N
    intro n hn
    exact le_trans (le_of_lt (hN n hn)) ((zpow_le_zpow_iff_right₀ (Nat.one_lt_cast.mpr hp.out.one_lt)).mpr (Int.sub_le_self _ zero_le_one))
  · intro Hm _ hε
    obtain ⟨_, hm⟩ := PadicInt.exists_pow_neg_lt p hε
    obtain ⟨N, hN⟩ := Hm _
    use N
    intro n hn
    exact lt_of_le_of_lt (hN n hn) hm

private theorem Padic.uniformContinuous_then_nonzero_norm_le_pow
  {f : ℤ_[p] → ℚ_[p]} (hf : UniformContinuous f) :
     ∀ s : ℕ, ∃ t : ℕ, t ≠ 0 ∧ ∀ b a : ℤ_[p], ‖a - b‖ ≤ p^(-t : ℤ) → ‖f a - f b‖ ≤ p^(-s : ℤ) := by
  simp_rw [Metric.uniformContinuous_iff, dist_eq_norm_sub] at hf
  intro s
  specialize hf ((p : ℝ)^(-s : ℤ)) (zpow_pos (Nat.cast_pos.mpr hp.out.pos) _)
  obtain ⟨δ, ⟨hδ, hf⟩⟩ := hf
  obtain ⟨t, ht⟩ := (PadicInt.exists_pow_neg_lt p hδ)
  use t + 1
  apply And.intro (Nat.add_one_ne_zero _)
  intro a b
  specialize @hf b a
  intro h
  have : ‖b - a‖ < δ := by
    calc
      _ ≤ _ := h
      _ < _ := by
        rw [Nat.cast_add, Nat.cast_one, neg_add, zpow_add₀ (Nat.cast_ne_zero.mpr hp.out.ne_zero)]
        apply mul_lt_of_lt_of_le_one_of_nonneg ht (zpow_le_one_of_nonpos₀ (Nat.one_le_cast.mpr hp.out.one_le) (Left.neg_nonpos_iff.mpr Int.one_nonneg))
        simp only [zpow_neg, zpow_natCast, inv_nonneg, Nat.cast_nonneg, pow_nonneg]
  exact le_of_lt (hf this)

------------------------------------------------------------------

private theorem bojanic_8 (f : C(ℤ_[p], ℚ_[p])) :
    ∀ s : ℕ, ∃ t : ℕ, t ≠ 0 ∧ ∀ (x : ℤ_[p]), ‖f (x + p^t) - f x‖ ≤ p^(-s : ℤ) := by
  intro s
  obtain ⟨t, ⟨ht', ht⟩⟩ := Padic.uniformContinuous_then_nonzero_norm_le_pow (CompactSpace.uniformContinuous_of_continuous f.continuous) s
  use t
  apply And.intro ht'
  intro x
  specialize ht x (x + p^t)
  rw [add_sub_cancel_left, PadicInt.norm_p_pow] at ht
  exact ht (le_refl _)

private theorem bojanic_10 (f : C(ℤ_[p], ℚ_[p])) (n : ℕ) (t : ℕ):
    ((p ^ t).choose (p^t)) • δ_[1]^[p^t] (δ_[1]^[n] f) 0 = - ∑ k ∈ Finset.range (p^t - 1), ((p^t).choose (k + 1)) • δ_[1]^[k + 1] (δ_[1]^[n] f) 0 + ∑ k ∈ Finset.range (n + 1), ((-1 : ℤ)^(n - k) * (n.choose k)) • (f (p^t • 1 + k • 1) - f (0 + k • 1)) := by
  simp_rw [smul_sub, Finset.sum_sub_distrib, ← fwdDiff_iter_eq_sum_shift]
  rw [add_sub, neg_add_eq_sub, sub_sub, eq_sub_iff_add_eq, add_comm]
  have : ((p ^ t).choose 0) • δ_[1]^[0] (δ_[1]^[n] f) = δ_[1]^[n] f := by
    simp_rw [Nat.choose_zero_right, Function.iterate_zero_apply, one_smul]
  nth_rw 2 [← this]
  have : ∑ k ∈ Finset.range (p ^ t), (p ^ t).choose (k) • δ_[1]^[k] (δ_[1]^[n] f) 0 = ∑ k ∈ Finset.range (p ^ t - 1), (p ^ t).choose (k + 1) • δ_[1]^[k + 1] (δ_[1]^[n] f) 0 + ((p ^ t).choose 0 • δ_[1]^[0] (δ_[1]^[n] f)) 0 := by
    rw [← Nat.succ_pred_eq_of_pos (Nat.pow_pos hp.out.pos), Finset.sum_range_succ']
    simp only [Nat.pred_eq_sub_one, Nat.succ_eq_add_one, Function.iterate_succ_apply, nsmul_eq_mul, Nat.choose_zero_right, Function.iterate_zero_apply, one_smul, add_tsub_cancel_right]
  rw [← this, ← Finset.sum_range_succ, ← shift_eq_sum_fwdDiff_iter, nsmul_eq_mul, Nat.cast_pow, zero_add]

private theorem bojanic_11 (f : C(ℤ_[p], ℚ_[p])) :
    ∀ s : ℕ, ∃ (t : ℕ) (ht : t ≠ 0), ∀ n : ℕ, ‖δ_[1]^[p ^ t + n] f 0‖ ≤ max (Finset.sup' (Finset.range (p^t - 1)) (Finset.nonempty_range_iff.mpr (Nat.sub_ne_zero_of_lt (Nat.one_lt_pow ht hp.out.one_lt))) (fun j : ℕ ↦ (p : ℝ)^(-1 : ℤ) * ‖δ_[1]^[j + 1 + n] f 0‖)) ((p : ℝ)^(-s : ℤ)) := by
  intro s
  obtain ⟨t, ⟨ht, ht'⟩⟩ := bojanic_8 f s
  use t
  use ht
  intro n
  have hpt : p^t - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (lt_of_lt_of_le (Nat.one_lt_pow ht Nat.one_lt_two) (Nat.pow_le_pow_of_le_left hp.out.two_le _))
  have hpt' : Finset.Nonempty (Finset.range (p^t - 1)) := Finset.nonempty_range_iff.mpr hpt
  have hn' : Finset.Nonempty (Finset.range (n + 1)) := Finset.nonempty_range_succ
  calc
    _ ≤ max ‖∑ x ∈ Finset.range (p ^ t - 1), -((p ^ t).choose (x + 1) • δ_[1]^[x + 1 + n] f 0)‖ ‖∑ x ∈ Finset.range (n + 1), ((-1 : ℤ) ^ (n - x) * (n.choose x)) • (f (p ^ t + x) - f x)‖ := by
      have bojanic_10 := bojanic_10 f n t
      simp_rw [nsmul_one, Nat.choose_self, one_smul, zero_add, ← Function.iterate_add_apply, ← Finset.sum_neg_distrib, Nat.cast_pow] at bojanic_10
      rw [bojanic_10]
      exact padicNormE.nonarchimedean _ _
    _ ≤ max (Finset.sup' (Finset.range (p^t - 1)) hpt' (fun j : ℕ ↦ ‖-((p ^ t).choose (j + 1) • δ_[1]^[j + 1 + n] f 0)‖)) (Finset.sup' (Finset.range (n + 1)) hn' (fun j : ℕ ↦ ‖((-1 : ℤ) ^ (n - j) * (n.choose j)) • (f (p ^ t + j) - f j)‖)) := by
      apply max_le_max
      · apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonempty (Finset.Aesop.range_nonempty hpt)
        intro _ hi
        apply Finset.le_sup' _ hi
      · apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonempty (Finset.Aesop.range_nonempty (Nat.add_one_ne_zero _))
        intro _ hi
        apply Finset.le_sup' _ hi
    _ ≤ max (Finset.sup' (Finset.range (p^t - 1)) hpt' (fun j : ℕ ↦ ‖(p ^ t).choose (j + 1) • δ_[1]^[j + 1 + n] f 0‖)) (Finset.sup' (Finset.range (n + 1)) hn' (fun j : ℕ ↦ ‖(n.choose j : ℚ_[p])‖ * ‖f (p ^ t + j) - f j‖)) := by
      apply max_le_max
      · simp_rw [norm_neg, le_refl]
      · simp only [Int.reduceNeg, zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast, padicNormE.mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, le_refl]
    _ ≤ max (Finset.sup' (Finset.range (p^t - 1)) hpt' (fun j : ℕ ↦ ‖(p ^ t).choose (j + 1) • δ_[1]^[j + 1 + n] f 0‖)) (Finset.sup' (Finset.range (n + 1)) hn' (fun j : ℕ ↦ ‖f (p ^ t + j) - f j‖)) := by
      apply max_le_max (le_refl _)
      simp_rw [Finset.sup'_le_iff]
      intro a _
      calc
        _ ≤ _ := mul_le_mul_of_nonneg_right (padicNormE.norm_int_le_one _) (norm_nonneg _)
        _ ≤ _ := by
          rw [one_mul, Finset.le_sup'_iff]
          use a
    _ ≤ _ := by
      apply max_le_max
      · rw [Finset.sup'_le_iff]
        intro a ha
        rw [Finset.le_sup'_iff]
        use a
        apply And.intro ha
        rw [nsmul_eq_mul, padicNormE.mul]
        calc
          _ ≤ (p : ℝ)^(-(1 : ℕ) : ℤ) * ‖δ_[1]^[a + 1 + n] f 0‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            have (k n : ℕ) : ‖(k : ℚ_[p])‖ ≤ (p : ℝ) ^ (-n : ℤ) ↔ (p ^ n : ℤ) ∣ k := padicNormE.norm_int_le_pow_iff_dvd _ _
            rw [this, pow_one]
            exact Nat.cast_dvd_cast (Nat.Prime.dvd_choose_pow hp.out (Nat.add_one_ne_zero _) (Nat.ne_of_lt (Nat.lt_sub_iff_add_lt.mp (Finset.mem_range.mp ha))))
          _ ≤ _ := by
            simp_rw [Nat.cast_one, le_refl]
      · rw [Finset.sup'_le_iff]
        intro _ _
        rw [add_comm]
        exact ht' _

private theorem bojanic_12 (f : C(ℤ_[p], ℚ_[p])) {y : ℤ_[p]} (hy' : ‖f y‖ = ‖f‖)
  (hb : Padic.addValuation (f y) = (0 : ℤ)) (s : ℕ) :
    ∃ t, ∀ j ≤ s, ∀ (n : ℕ), j * p ^ t ≤ n → ‖δ_[1]^[n] (⇑f) 0‖ ≤ ↑p ^ (-j : ℤ) := by
  obtain ⟨t, ⟨ht', ht⟩⟩ := bojanic_11 f s
  use t
  intro j
  induction' j with j hj
  . simp_rw [zero_mul, zero_le, true_implies, CharP.cast_eq_zero, ← Padic.le_addValuation, ← hb,
      Padic.addValuation_le_addValuation, hy']
    exact IsUltrametricDist.norm_fwdDiff_iter_apply_le _ _ _
  · intro hj' n hn
    specialize ht (n - p^t)
    simp_rw [Nat.add_sub_of_le (le_trans (Nat.le_mul_of_pos_left _ (Nat.zero_lt_succ _)) hn), le_max_iff, Finset.le_sup'_iff] at ht
    cases ht with
    | inl H =>
      obtain ⟨k, ⟨_, hk⟩⟩ := H
      have : j * p ^ t ≤ k + 1 + (n - p ^ t) := by
        apply le_add_left (Nat.le_sub_of_add_le _)
        calc
          _ = _ := by rw[add_mul, one_mul]
          _ ≤ _ := hn
      calc
        _ ≤ _ := hk
        _ ≤ (p : ℝ)^(-1 : ℤ) * (p : ℝ)^(-j : ℤ) := by
          rw [mul_le_mul_iff_of_pos_left _]
          · exact (hj (le_of_lt (Nat.add_one_le_of_lt hj'))) _ this
          · simp_rw [zpow_neg, inv_pos, zpow_one]
            exact Nat.cast_pos.mpr hp.out.pos
        _ = _ := by
          simp_rw [← Real.rpow_intCast, ← Real.rpow_add (Nat.cast_pos.mpr hp.out.pos), Int.cast_neg,
            Int.cast_one, Int.cast_natCast, Nat.cast_add, Nat.cast_one, neg_add_rev]
    | inr H =>
      exact le_trans H (zpow_le_zpow_right₀
        (Nat.one_le_cast.mpr hp.out.one_le) (Int.neg_le_neg (Nat.cast_le.mpr hj')))

------------------------------------------------------------------------------------------

theorem PadicInt.fwdDiff_tendsto_zero (f : C(ℤ_[p], ℚ_[p])) :
    Filter.Tendsto (fun k ↦ δ_[1]^[k] f 0) Filter.atTop (nhds 0) := by
  simp_rw [Padic.tendsto_atTop_norm_le_pow, sub_zero]
  obtain ⟨y, hy'⟩ := ContinuousMap.exists_norm_eq_norm_apply f
  have hy := ContinuousMap.norm_coe_le_norm f
  rw [← hy'] at hy

  cases hb : Padic.addValuation (f y) with
  | top =>
    have : f = (fun (_ : ℤ_[p]) ↦ (0 : ℚ_[p])) := by
      by_contra! k
      have : ∃ x : ℤ_[p], f x ≠ 0 := by
        contrapose! k
        exact funext k
      obtain ⟨x, hx⟩ := this
      have l : Padic.addValuation (f x) = ⊤ := by
        rw [eq_top_iff, ← hb, Padic.addValuation_le_addValuation]
        exact hy _
      have l' : Padic.addValuation (f x) ≠ ⊤ := by
        simp_rw [Padic.addValuation.apply hx, ne_eq, WithTop.coe_ne_top, not_false_eq_true]
      exact l' l
    rw [this]
    simp only [fwdDiff_iter_const_zero, norm_zero, zpow_neg, zpow_natCast, inv_nonneg, Nat.cast_nonneg, pow_nonneg, implies_true, exists_const]
  | coe b =>
    wlog hb' : b = 0
    · rw [← ne_eq] at hb'
      specialize this ((p^(-b : ℤ) : ℚ_[p]) • f) y
      simp_rw [ContinuousMap.coe_smul, norm_smul, Pi.smul_apply, smul_eq_mul, padicNormE.mul, padicNormE.norm_p_zpow, neg_neg, hy', true_implies] at this
      have Hx : ∀ (x : ℤ_[p]), (p : ℝ)^b * ‖f x‖ ≤ (p : ℝ)^b * ‖f‖ := by
        intro _
        rw [mul_le_mul_iff_of_pos_left]
        · rw [← hy']
          exact hy _
        · rw [← Real.rpow_intCast]
          exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.out.pos) _
      specialize this Hx 0
      have Hb : Padic.addValuation ((p : ℚ_[p]) ^ (-b : ℤ) * f y) = (0 : ℤ) := by
        rw [eq_comm, Padic.eq_addValuation_iff_norm_eq_pow_neg, padicNormE.mul,padicNormE.norm_p_zpow, neg_neg, neg_zero, zpow_zero, IsUnit.mul_eq_one_iff_inv_eq]
        · rw [← zpow_neg, eq_comm, ← Padic.eq_addValuation_iff_norm_eq_pow_neg, eq_comm]
          exact hb
        · rw [isUnit_iff_ne_zero, ← Real.rpow_intCast, Real.rpow_ne_zero]
          · rw [ne_eq, Nat.cast_eq_zero, ← ne_eq]
            exact hp.out.ne_zero
          · simp_rw [Nat.cast_nonneg]
          · rw [ne_eq, Int.cast_eq_zero, ← ne_eq]
            exact hb'
      simp_rw [Hb, true_implies] at this
      intro m
      obtain ⟨N, hN⟩ := this (Nat.floor (m - b))
      use N
      intro n hn
      specialize hN n hn
      rw [fwdDiff_iter_const_smul, Pi.smul_apply, smul_eq_mul, padicNormE.mul,
        padicNormE.norm_p_zpow, neg_neg, mul_comm] at hN
      have Hp : (p : ℝ)^b > 0 := by
        rw [← Real.rpow_intCast]
        exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.out.pos) _
      rw [← mul_le_mul_iff_of_pos_right Hp]
      apply le_trans hN
      simp_rw [← Real.rpow_intCast, ← Real.rpow_add (Nat.cast_pos.mpr hp.out.pos),
        Real.rpow_le_rpow_left_iff (Nat.one_lt_cast.mpr hp.out.one_lt), Nat.floor_int,
        Int.ofNat_toNat, Int.cast_neg, Int.cast_max, Int.cast_sub, Int.cast_natCast, Int.cast_zero,
        le_neg_add_iff_add_le, add_neg_le_iff_le_add]
      rw [add_comm, ← sub_le_iff_le_add, le_max_iff]
      exact Or.inl (le_refl _)
    · rw [hb'] at hb
      intro m
      obtain ⟨t, ht⟩ := bojanic_12 f hy' hb m
      specialize ht m
      simp_rw [le_refl, true_implies] at ht
      use (m * p^t)

----------------------------------------------------------------------------------------------------------------------------------------------

theorem mahler_series_on_nat (f : C(ℤ_[p], ℚ_[p])) (n : ℕ) :
    f n = ∑' k : ℕ, δ_[1]^[k] f 0 / k.factorial * (descPochhammer ℤ_[p] k).eval (n : ℤ_[p]) := by
  simp_rw [descPochhammer_eval_eq_descFactorial, PadicInt.coe_natCast, div_mul_comm]
  have (n : ℕ) : n = ((n : ℚ) : ℚ_[p]) := by
    rw [Rat.cast_natCast]
  simp_rw [this, ← Padic.coe_div]
  have (n k : ℕ) : ((n.descFactorial k) : ℚ) / (k.factorial : ℚ) = n.choose k := by
    rw [Nat.choose_eq_descFactorial_div_factorial, Nat.cast_div (Nat.factorial_dvd_descFactorial n k) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))]
  simp_rw [this, Rat.cast_natCast]
  have (n : ℕ) : ∑' k : ℕ, (n.choose k) * δ_[1]^[k] f 0 = ∑ k ∈ Finset.range (n + 1), (n.choose k) * δ_[1]^[k] f 0 := by
    rw [tsum_eq_sum]
    intro k hk
    rw [Finset.mem_range, not_lt] at hk
    rw [mul_eq_zero, Nat.cast_eq_zero]
    exact Or.inl (Nat.choose_eq_zero_iff.mpr hk)
  rw [this]
  have := shift_eq_sum_fwdDiff_iter 1 f n 0
  simp_rw [nsmul_eq_mul, mul_one, zero_add] at this
  exact this

theorem tsum_sub_sum_nat {G : Type*} [AddCommGroup G] [TopologicalSpace G] [TopologicalAddGroup G] [T2Space G] (n : ℕ) {f : ℕ → G} (h : Summable f) :
    ∑' k : ℕ, f k - ∑ k ∈ Finset.range n, f k = ∑' k : ℕ, f (k + n) := sub_eq_of_eq_add' (Eq.symm (sum_add_tsum_nat_add n h))

theorem mahler_partial_sums_tendstoUniformly_mahler_series (f : C(ℤ_[p], ℚ_[p])) :
    TendstoUniformly (fun n x ↦ ∑ k ∈ Finset.range (n + 1), δ_[1]^[k] f 0 / k.factorial * (Polynomial.eval x (descPochhammer ℤ_[p] k))) (fun x ↦ ∑' (k : ℕ), δ_[1]^[k] f 0 / k.factorial * (Polynomial.eval x (descPochhammer ℤ_[p] k))) Filter.atTop := by
  have h := PadicInt.fwdDiff_tendsto_zero f
  simp_rw [Metric.tendsto_atTop, dist_eq_norm_sub, sub_zero] at h
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε/2) (half_pos hε)
  simp_rw [Filter.eventually_atTop, ge_iff_le, dist_eq_norm_sub]
  use N
  intro n hn x
  have hf : Summable fun k ↦ δ_[1]^[k] f 0 / k.factorial * (Polynomial.eval x (descPochhammer ℤ_[p] k)) := by
    rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, Nat.cofinite_eq_atTop]
    simp_rw [div_mul_comm]
    have h := PadicInt.fwdDiff_tendsto_zero f
    simp_rw [NormedAddCommGroup.tendsto_atTop', sub_zero] at *
    intro ε hε
    obtain ⟨N, hN⟩ := h ε hε
    use N
    intro n hn
    rw [padicNormE.mul, norm_div, PadicInt.padic_norm_e_of_padicInt]
    calc
      _ ≤ _ := mul_le_of_le_one_left (norm_nonneg _) ((div_le_one (norm_pos_iff.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)))).mpr (PadicInt.norm_descPochhammer_le _ _))
      _ < _ := hN _ hn
  rw [tsum_sub_sum_nat _ hf]
  calc
    _ ≤ _ := IsUltrametricDist.norm_tsum_le _
    _ ≤ ⨆ k, ‖δ_[1]^[k + (n + 1)] f 0‖ := by
      apply Real.iSup_le
      · intro i
        calc
          _ ≤ ‖δ_[1]^[i + (n + 1)] f 0‖ := by
            rw [padicNormE.mul, norm_div, PadicInt.padic_norm_e_of_padicInt, div_mul_comm]
            exact mul_le_of_le_one_left (norm_nonneg _) (div_le_one_of_le₀ (PadicInt.norm_descPochhammer_le _ _) (norm_nonneg _))
          _ ≤ _ := by
            apply le_ciSup_of_le _ i (le_refl _)
            rw [BddAbove, Set.nonempty_def]
            use ‖f‖
            simp_rw [mem_upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
            intro _
            exact IsUltrametricDist.norm_fwdDiff_iter_apply_le _ _ _ _
      · apply Real.iSup_nonneg'
        use 0
        exact norm_nonneg _
    _ ≤ _ := by
      apply Real.iSup_le _ (div_nonneg (le_of_lt hε) zero_le_two)
      intro i
      apply le_of_lt
      apply hN (i + (n + 1))
      omega
    _ < _ := half_lt_self hε

theorem mahler_series_continuous (f : C(ℤ_[p], ℚ_[p])) :
    Continuous fun x ↦ ∑' (k : ℕ), δ_[1]^[k] f 0 / k.factorial * (Polynomial.eval x (descPochhammer ℤ_[p] k)) := by
  apply TendstoUniformly.continuous (mahler_partial_sums_tendstoUniformly_mahler_series _)
  rw [Filter.eventually_atTop]
  use 0
  intro _ _
  apply continuous_finset_sum (Finset.range _)
  intro _ _
  exact Continuous.mul continuous_const (Continuous.comp' (Continuous.subtype_val continuous_id') (Polynomial.continuous_eval₂ _ _))

theorem mahler_series_eq_fun (f : C(ℤ_[p], ℚ_[p])) :
    f = fun x ↦ ∑' k : ℕ, δ_[1]^[k] f 0 / k.factorial * (descPochhammer ℤ_[p] k).eval x := by
  apply DenseRange.equalizer PadicInt.denseRange_natCast (ContinuousMap.continuous f)
  · exact mahler_series_continuous _
  · ext _
    simp_rw [Function.comp_apply, mahler_series_on_nat]
