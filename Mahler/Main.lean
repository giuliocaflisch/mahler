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
    specialize hN n hn
    calc
      _ ≤ _:= le_of_lt hN
      _ ≤ _ := (zpow_le_zpow_iff_right₀ (Nat.one_lt_cast.mpr hp.out.one_lt)).mpr (Int.sub_le_self _ zero_le_one)
  · intro Hm ε hε
    obtain ⟨m, hm⟩ := PadicInt.exists_pow_neg_lt p hε
    obtain ⟨N, hN⟩ := Hm m
    use N
    intro n hn
    specialize hN n hn
    calc
      _ ≤ (p : ℝ)^(-m : ℤ) := hN
      _ < _ := hm

private theorem Padic.uniformContinuous_then_nonzero_norm_le_pow {f : ℤ_[p] → ℚ_[p]} :
    UniformContinuous f → ∀ s : ℕ, ∃ t : ℕ, t ≠ 0 ∧ ∀ b a : ℤ_[p], ‖a - b‖ ≤ p^(-t : ℤ) → ‖f a - f b‖ ≤ p^(-s : ℤ) := by
  simp_rw [Metric.uniformContinuous_iff, dist_eq_norm_sub]
  intro hf s
  specialize hf ((p : ℝ)^(-s : ℤ)) (zpow_pos (Nat.cast_pos.mpr hp.out.pos) _)
  obtain ⟨δ, ⟨hδ, hf⟩⟩ := hf
  obtain ⟨t, ht⟩ := (PadicInt.exists_pow_neg_lt p hδ)
  use t + 1
  apply And.intro (Nat.add_one_ne_zero _)
  intro a b
  specialize @hf b a
  intro hab
  have : ‖b - a‖ < δ := by
    calc
      _ ≤ _ := hab
      _ < _ := by
        rw [Nat.cast_add, Nat.cast_one, neg_add, zpow_add₀]
        · apply mul_lt_of_lt_of_le_one_of_nonneg ht (zpow_le_one_of_nonpos₀ (Nat.one_le_cast.mpr hp.out.one_le) (Left.neg_nonpos_iff.mpr Int.one_nonneg))
          simp only [zpow_neg, zpow_natCast, inv_nonneg, Nat.cast_nonneg, pow_nonneg]
        · rw [ne_eq, Nat.cast_eq_zero, ← ne_eq]
          exact hp.out.ne_zero
  exact le_of_lt (hf this)

------------------------------------------------------------------

private theorem bojanic_10 (f : C(ℤ_[p], ℚ_[p])) (n : ℕ) (t : ℕ):
    ((p ^ t).choose (p^t)) • δ_[1]^[p^t] (δ_[1]^[n] f) 0 = - ∑ k ∈ Finset.range (p ^ t - 1), ((p ^ t).choose (k + 1)) • δ_[1]^[k + 1] (δ_[1]^[n] f) 0 + ∑ k ∈ Finset.range (n + 1), ((-1 : ℤ) ^ (n - k) * (n.choose k)) • (f (p ^ t • 1 + k • 1) - f (0 + k • 1)) := by
  simp_rw [smul_sub, Finset.sum_sub_distrib, ← fwdDiff_iter_eq_sum_shift]
  rw [add_sub, neg_add_eq_sub, sub_sub, eq_sub_iff_add_eq, add_comm]
  have : ((p ^ t).choose 0) • δ_[1]^[0] (δ_[1]^[n] f) = δ_[1]^[n] f := by
    simp_rw [Nat.choose_zero_right, Function.iterate_zero_apply, one_smul]
  nth_rw 2 [← this]
  have : ∑ k ∈ Finset.range (p ^ t), (p ^ t).choose (k) • δ_[1]^[k] (δ_[1]^[n] f) 0 = ∑ k ∈ Finset.range (p ^ t - 1), (p ^ t).choose (k + 1) • δ_[1]^[k + 1] (δ_[1]^[n] f) 0 + ((p ^ t).choose 0 • δ_[1]^[0] (δ_[1]^[n] f)) 0 := by
    rw [← Nat.succ_pred_eq_of_pos (Nat.pow_pos hp.out.pos), Finset.sum_range_succ']
    simp only [Nat.pred_eq_sub_one, Nat.succ_eq_add_one, Function.iterate_succ, Function.comp_apply, nsmul_eq_mul, Nat.choose_zero_right, Function.iterate_zero_apply, one_smul, add_tsub_cancel_right]
  rw [← this, ← Finset.sum_range_succ, ← shift_eq_sum_fwdDiff_iter, nsmul_eq_mul, Nat.cast_pow, zero_add]

private theorem bojanic_11 (f : C(ℤ_[p], ℚ_[p])):
    ∀ s : ℕ, ∃ (t : ℕ) (ht : t ≠ 0), ∀ n : ℕ, ‖δ_[1]^[p ^ t + n] f 0‖ ≤ max (Finset.sup' (Finset.range (p^t - 1)) (Finset.nonempty_range_iff.mpr (Nat.sub_ne_zero_of_lt (Nat.one_lt_pow ht hp.out.one_lt))) (fun j : ℕ ↦ (p : ℝ)^(-1 : ℤ) * ‖δ_[1]^[j + 1 + n] f 0‖)) ((p : ℝ)^(-(s : ℤ))) := by
  have bojanic_8 : ∀ s : ℕ, ∃ t : ℕ, t ≠ 0 ∧ ∀ (x : ℤ_[p]),  ‖f (x + (p : ℤ_[p])^t) - f x‖ ≤ p^(-(s : ℤ)) := by
    intro s
    obtain ⟨t, ⟨ht', ht⟩⟩ := Padic.uniformContinuous_then_nonzero_norm_le_pow (CompactSpace.uniformContinuous_of_continuous f.continuous) s
    use t
    apply And.intro ht'
    intro x
    specialize ht x (x + p^t)
    simp_rw [add_sub_cancel_left, PadicInt.norm_p_pow] at ht
    exact ht (le_refl _)

  intro s
  specialize bojanic_8 s
  obtain ⟨t, ⟨ht', ht⟩⟩ := bojanic_8
  use t
  use ht'
  intro n

  have k := bojanic_10 f n t
  simp_rw [nsmul_one, Nat.choose_self, one_smul, zero_add, ← Function.iterate_add_apply, ← Finset.sum_neg_distrib, Nat.cast_pow] at k

  have hpt : p^t - 1 ≠ 0 := by
    apply Nat.sub_ne_zero_of_lt
    calc
      _ < 2^t := Nat.one_lt_pow ht' Nat.one_lt_two
      _ ≤ _ := Nat.pow_le_pow_of_le_left hp.out.two_le _

  have hpt' : Finset.Nonempty (Finset.range (p^t - 1)) := Finset.nonempty_range_iff.mpr hpt
  have hn' : Finset.Nonempty (Finset.range (n + 1)) := Finset.nonempty_range_succ

  calc
    _ ≤ max ‖∑ x ∈ Finset.range (p ^ t - 1), -((p ^ t).choose (x + 1) • δ_[1]^[x + 1 + n] f 0)‖ ‖∑ x ∈ Finset.range (n + 1), ((-1 : ℤ) ^ (n - x) * (n.choose x)) • (f (p ^ t + x) - f x)‖ := by
      rw [k]
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
      intro a ha
      calc
        _ ≤ 1 * ‖f (p ^ t + a) - f a‖ := by
          apply mul_le_mul_of_nonneg_right (padicNormE.norm_int_le_one _)
          simp only [norm_nonneg]
        _ = ‖f (p ^ t + a) - f a‖ := by
          rw [one_mul]
        _ ≤ _ := by
          rw [Finset.le_sup'_iff]
          use a
    _ ≤ _ := by
      apply max_le_max
      · simp only [Finset.sup'_le_iff]
        intro a ha
        simp only [Finset.le_sup'_iff]
        use a
        apply And.intro ha
        simp only [nsmul_eq_mul, padicNormE.mul]
        calc
          _ ≤ (p : ℝ)^(-(1 : ℕ) : ℤ) * ‖δ_[1]^[a + 1 + n] f 0‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            have (k n : ℕ) : ‖(k : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ)) ↔ (p ^ n : ℤ) ∣ k := padicNormE.norm_int_le_pow_iff_dvd _ _
            rw [this, pow_one]
            exact Nat.cast_dvd_cast (Nat.Prime.dvd_choose_pow hp.out (Nat.add_one_ne_zero _) (Nat.ne_of_lt (Nat.lt_sub_iff_add_lt.mp (Finset.mem_range.mp ha))))
          _ ≤ _ := by
            simp only [Nat.cast_one, le_refl]
      · simp only [Finset.sup'_le_iff]
        intro a _
        specialize ht a
        rw [add_comm]
        simp only [nsmul_one, Nat.cast_pow, zpow_neg, zpow_natCast]
        simp only [smul_eq_mul, zpow_neg, zpow_natCast] at ht
        exact ht

------------------------------------------------------------------------------------------

private theorem PadicInt.fwdDiff_tendsto_zero (f : C(ℤ_[p], ℚ_[p])) :
    Filter.Tendsto (fun k ↦ δ_[1]^[k] f 0) Filter.atTop (nhds 0) := by
  ---
  simp_rw [Padic.tendsto_atTop_norm_le_pow, sub_zero]
  obtain ⟨y, hy'⟩ := ContinuousMap.exists_norm_eq_norm_apply f
  have hy := ContinuousMap.norm_coe_le_norm f
  rw [← hy'] at hy

  cases hb : Padic.addValuation (f y) with
  | top =>
    have : f = (fun (_ : ℤ_[p]) ↦ (0 : ℚ_[p])) := by
      by_contra k
      have : ∃ x : ℤ_[p], f x ≠ 0 := by
        contrapose! k
        ext x
        apply k
      obtain ⟨x, hx⟩ := this
      have l : Padic.addValuation (f x) = ⊤ := by
        rw [eq_top_iff, ← hb, Padic.addValuation_le_addValuation]
        exact hy _
      have l' : Padic.addValuation (f x) ≠ ⊤ := by
        simp only [Padic.addValuation.apply hx, ne_eq, WithTop.coe_ne_top, not_false_eq_true]
      exact l' l
    rw [this]
    simp only [ge_iff_le, fwdDiff_iter_const_zero, norm_zero, zpow_neg, zpow_natCast, inv_nonneg, Nat.cast_nonneg, pow_nonneg, implies_true, exists_const]
  | coe b =>
    wlog hb' : b = 0
    · rw [← ne_eq] at hb'
      specialize this ((p^(-b : ℤ) : ℚ_[p]) • f) y
      simp only [ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, padicNormE.mul, padicNormE.norm_p_zpow, zpow_natCast, neg_neg, norm_smul, hy', true_implies] at this
      have Hx : ∀ (x : ℤ_[p]), (p : ℝ)^b * ‖f x‖ ≤ (p : ℝ)^b * ‖f‖ := by
        intro x
        specialize hy x
        apply (mul_le_mul_iff_of_pos_left ?_).mpr
        · rw [← hy']
          exact hy
        · rw [← Real.rpow_intCast]
          exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.out.pos) _
      specialize this Hx 0
      have Hb : Padic.addValuation ((p : ℚ_[p]) ^ (-b : ℤ) * f y) = (0 : ℤ) := by
        ---
        rw [eq_comm, Padic.eq_addValuation_iff_norm_eq_pow_neg]
        simp only [zpow_neg, padicNormE.mul, norm_inv, padicNormE.norm_p_zpow, inv_inv, neg_zero, zpow_zero]
        apply (IsUnit.mul_eq_one_iff_inv_eq _).mpr _
        · rw [isUnit_iff_ne_zero, ← Real.rpow_intCast, Real.rpow_ne_zero]
          · rw [ne_eq, Nat.cast_eq_zero, ← ne_eq]
            exact hp.out.ne_zero
          · simp only [Nat.cast_nonneg]
          · simp only [ne_eq, Int.cast_eq_zero]
            simp only [← ne_eq]
            exact hb'
        · rw [← zpow_neg, eq_comm, ← Padic.eq_addValuation_iff_norm_eq_pow_neg, eq_comm]
          exact hb
      simp only [Hb, WithTop.coe_zero, true_implies] at this
      intro m
      specialize this (Nat.floor (m - b))
      obtain ⟨N, hN⟩ := this
      use N
      intro n hn
      specialize hN n hn
      simp only [fwdDiff_iter_const_smul, Pi.smul_apply, smul_eq_mul, padicNormE.mul, neg_neg, padicNormE.norm_p_zpow] at hN
      rw [mul_comm] at hN
      have Hp : (p : ℝ)^b > 0 := by
        simp only [← Real.rpow_intCast]
        exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hp.out.pos) _
      rw [← mul_le_mul_iff_of_pos_right Hp]
      calc
        _ ≤ (p : ℝ)^(-(Nat.floor (m - b) : ℤ)) := by
          apply hN
        _ ≤ _ := by
          simp_rw [← Real.rpow_intCast, ← Real.rpow_add (Nat.cast_pos.mpr hp.out.pos),
            Real.rpow_le_rpow_left_iff (Nat.one_lt_cast.mpr hp.out.one_lt), Nat.floor_int,
            Int.ofNat_toNat, Int.cast_neg, Int.cast_max, Int.cast_sub, Int.cast_natCast,
            Int.cast_zero, le_neg_add_iff_add_le, add_neg_le_iff_le_add]
          rw [add_comm, ← sub_le_iff_le_add]
          simp_rw [le_max_iff, le_refl, tsub_le_iff_right, zero_add, true_or]
    · rw [hb'] at hb
      have l' : ∀ s : ℕ, ∃ t : ℕ, t ≠ 0 ∧ ∀ j : ℕ, j ≤ s → ∀ n : ℕ, (j * p ^ t ≤ n → ‖δ_[1]^[n] f 0‖ ≤ (p : ℝ) ^ (- j : ℤ)) := by
        intro s
        obtain ⟨t, ⟨ht', ht⟩⟩ := bojanic_11 f s
        use t
        apply And.intro ht'
        intro j
        induction' j with j hj
        . simp_rw [zero_mul, zero_le, true_implies, CharP.cast_eq_zero, ← Padic.le_addValuation, ← hb, Padic.addValuation_le_addValuation, hy']
          exact IsUltrametricDist.norm_fwdDiff_iter_apply_le _ _ _
        · intro hj' n hn
          specialize ht (n - p^t)
          have : p ^ t + (n - p ^ t) = n := by
            apply Nat.add_sub_of_le
            calc
              _ ≤ (j + 1) * p^t := by
                apply Nat.le_mul_of_pos_left
                simp_rw [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true]
              _ ≤ _ := hn
          simp_rw [this, le_max_iff, Finset.le_sup'_iff] at ht
          specialize hj (le_of_lt (Nat.add_one_le_of_lt hj'))
          cases ht with
          | inl H =>
            obtain ⟨k, ⟨_, hk⟩⟩ := H
            have : j * p ^ t ≤ k + 1 + (n - p ^ t) := by
              apply le_add_left
              apply Nat.le_sub_of_add_le
              calc
                _ = (j + 1) * p ^ t := by
                  rw[add_mul, one_mul]
                _ ≤ _ := hn
            specialize hj (k + 1 + (n - p ^ t)) this
            calc
              _ ≤ (p : ℝ)^(-1 : ℤ) * ‖δ_[1]^[k + 1 + (n - p ^ t)] f 0‖ := hk
              _ ≤ (p : ℝ)^(-1 : ℤ) * (p : ℝ)^(-j : ℤ) := by
                rw [mul_le_mul_iff_of_pos_left _]
                · exact hj
                · simp only [Int.reduceNeg, zpow_neg, zpow_one, inv_pos, Nat.cast_pos]
                  exact hp.out.pos
              _ = _ := by
                simp_rw [← Real.rpow_intCast]
                rw [← Real.rpow_add]
                simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one, Int.cast_natCast, Nat.cast_add, Nat.cast_one, neg_add_rev, Int.cast_add]
                exact Nat.cast_pos.mpr hp.out.pos
          | inr H =>
            calc
              _ ≤ _ := H
              _ ≤ _ := zpow_le_zpow_right₀ (Nat.one_le_cast.mpr hp.out.one_le) (Int.neg_le_neg (Nat.cast_le.mpr hj'))
      intro m
      specialize l' m
      obtain ⟨t, ⟨_, ht⟩⟩ := l'
      specialize ht m
      simp_rw [le_refl, true_implies] at ht
      use (m * p^t)

----------------------------------------------------------------------------------------------------------------------------------------------

private theorem natural_mahler (f : C(ℤ_[p], ℚ_[p])) (n : ℕ) :
    f n = ∑' k : ℕ, δ_[1]^[k] f 0 / k.factorial * (descPochhammer ℤ_[p] k).eval (n : ℤ_[p]) := by
  simp_rw [descPochhammer_eval_eq_descFactorial, PadicInt.coe_natCast, div_mul_comm]
  have (n : ℕ) : n = ((n : ℚ) : ℚ_[p]) := by
    simp only [Rat.cast_natCast]
  simp_rw [this, ← Padic.coe_div]
  have (n k : ℕ) :
      ((n.descFactorial k) : ℚ) / (k.factorial : ℚ) = n.choose k := by
    simp_rw [Nat.choose_eq_descFactorial_div_factorial]
    rw [Nat.cast_div (Nat.factorial_dvd_descFactorial n k)]
    simp_rw [ne_eq, Nat.cast_eq_zero, ← ne_eq]
    apply Nat.factorial_ne_zero
  simp_rw [this, Rat.cast_natCast]
  have (n : ℕ) : ∑' k : ℕ, (n.choose k) * δ_[1]^[k] f 0 = ∑ k ∈ Finset.range (n + 1), (n.choose k) * δ_[1]^[k] f 0 := by
    rw [tsum_eq_sum]
    intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    simp only [mul_eq_zero, Nat.cast_eq_zero]
    exact Or.intro_left _ (Nat.choose_eq_zero_iff.mpr hk)
  simp_rw [this]
  have := shift_eq_sum_fwdDiff_iter 1 f n 0
  simp only [nsmul_eq_mul, mul_one, zero_add] at this
  exact this

theorem my_mahler (f : C(ℤ_[p], ℚ_[p])) :
    f = fun x ↦ ∑' k : ℕ, δ_[1]^[k] f 0 / k.factorial * (descPochhammer ℤ_[p] k).eval x := by
  apply DenseRange.equalizer PadicInt.denseRange_natCast (ContinuousMap.continuous f)
  · have : TendstoUniformly (fun n x ↦ ∑ k ∈ Finset.range (n + 1), δ_[1]^[k] f 0 / k.factorial * (Polynomial.eval x (descPochhammer ℤ_[p] k))) (fun x ↦ ∑' (k : ℕ), δ_[1]^[k] f 0 / k.factorial * (Polynomial.eval x (descPochhammer ℤ_[p] k))) Filter.atTop := by
      sorry
      /-
      have h := PadicInt.fwdDiff_tendsto_zero 1 f
      simp_rw [Metric.tendsto_atTop, dist_eq_norm_sub, sub_zero] at h

      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      have : ε/2 > 0 := by
        apply div_pos_iff.mpr
        apply Or.intro_left
        exact (And.intro hε zero_lt_two)
      specialize h (ε/2) this
      obtain ⟨N, hN⟩ := h
      simp_rw [Filter.eventually_atTop, ge_iff_le, dist_eq_norm_sub]
      use N
      intro n hn x

      have hf : Summable fun k ↦ δ_[1]^[k] f 0 / k.factorial * (Polynomial.eval x (descPochhammer ℤ_[p] k)) := by
        rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero, Nat.cofinite_eq_atTop]
        simp_rw [div_mul_comm]
        have h := PadicInt.fwdDiff_tendsto_zero 1 f
        simp_rw [NormedAddCommGroup.tendsto_atTop', sub_zero] at *
        intro ε hε
        specialize h ε hε
        obtain ⟨N, hN⟩ := h
        use N
        intro n hn
        rw [padicNormE.mul, norm_div, PadicInt.padic_norm_e_of_padicInt]
        calc
          _ ≤ ‖δ_[1]^[n] f 0‖ := by
            exact mul_le_of_le_one_left (norm_nonneg _) ((div_le_one (norm_pos_iff.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)))).mpr (PadicInt.norm_descPochhammer_le _ _))
          _ < _ := hN _ hn

      have hf' : Summable fun k ↦ δ_[1]^[k + (n + 1)] f 0 / (k + (n + 1)).factorial * (Polynomial.eval x (descPochhammer ℤ_[p] (k + (n + 1)))) := by
        have : (fun k ↦ δ_[1]^[k + (n + 1)] f 0 / (k + (n + 1)).factorial * (Polynomial.eval x (descPochhammer ℤ_[p] (k + (n + 1))))) = (fun k ↦ δ_[1]^[k] f 0 / k.factorial * (Polynomial.eval x (descPochhammer ℤ_[p] k))) ∘ (fun k ↦ k + (n + 1)) := by
          exact rfl
        rw [this]
        exact Summable.comp_injective hf (add_left_injective _)

      rw [tsum_sub_sum _ hf, IsUltrametricDist.norm_tsum_le_iff _ hf']
      intro k
      rw [padicNormE.mul, norm_div, PadicInt.padic_norm_e_of_padicInt, div_mul_comm]
      calc
        _ ≤ ‖δ_[1]^[k + n + 1] f 0‖ := mul_le_of_le_one_left (norm_nonneg _) ((div_le_one (norm_pos_iff.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)))).mpr (PadicInt.norm_descPochhammer_le _ _))
        _ < _ := by
          apply hN _
          omega
      -/
    apply TendstoUniformly.continuous this
    · simp_rw [Filter.eventually_atTop, ge_iff_le]
      use 0
      intro _ _
      apply continuous_finset_sum (Finset.range _)
      intro _ _
      exact Continuous.mul continuous_const (Continuous.comp' (Continuous.subtype_val continuous_id') (Polynomial.continuous_eval₂ _ _))
  · ext _
    simp_rw [Function.comp_apply]
    rw [natural_mahler]
