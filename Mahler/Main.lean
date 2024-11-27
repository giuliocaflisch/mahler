/-

Authors: Giulio Caflisch, David Loeffler
-/
import Mahler.ForwardDiff
import Mahler.Help
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Analysis.NormedSpace.FunctionSeries
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.NumberTheory.Padics.MahlerBasis

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

private theorem Padic.bojanic (h : ℤ_[p]) (f : C(ℤ_[p], ℚ_[p])) (n : ℕ) (t : ℕ):
    ((p ^ t).choose (p^t)) • δ_[h]^[p^t] (δ_[h]^[n] f) 0 = - ∑ k ∈ Finset.range (p ^ t - 1), ((p ^ t).choose (k + 1)) • δ_[h]^[k + 1] (δ_[h]^[n] f) 0 + ∑ k ∈ Finset.range (n + 1), ((-1 : ℤ) ^ (n - k) * (n.choose k)) • (f (p ^ t • h + k • h) - f (0 + k • h)) := by
  simp_rw [smul_sub, Finset.sum_sub_distrib, ← fwdDiff_iter_eq_sum_shift]
  rw [add_sub, neg_add_eq_sub, sub_sub, eq_sub_iff_add_eq, add_comm]
  have k' : ((p ^ t).choose 0) • δ_[h]^[0] (δ_[h]^[n] f) = δ_[h]^[n] f := by
    simp_rw [Nat.choose_zero_right, Function.iterate_zero_apply, one_smul]
  nth_rw 2 [← k']
  have k' : ∑ k ∈ Finset.range (p ^ t), (p ^ t).choose (k) • δ_[h]^[k] (δ_[h]^[n] f) 0 = ∑ k ∈ Finset.range (p ^ t - 1), (p ^ t).choose (k + 1) • δ_[h]^[k + 1] (δ_[h]^[n] f) 0 + ((p ^ t).choose 0 • δ_[h]^[0] (δ_[h]^[n] f)) 0 := by
    have : Nat.succ (Nat.pred (p^t)) = p^t := Nat.succ_pred_eq_of_pos (Nat.pow_pos hp.out.pos)
    rw [← this, Finset.sum_range_succ']
    simp only [Nat.pred_eq_sub_one, Nat.succ_eq_add_one, Function.iterate_succ, Function.comp_apply, nsmul_eq_mul, Nat.choose_zero_right, Function.iterate_zero_apply, one_smul, add_tsub_cancel_right]
  rw [← k', ← Finset.sum_range_succ, ← shift_eq_sum_fwdDiff_iter]
  simp_rw [nsmul_eq_mul, Nat.cast_pow, zero_add]

theorem Padic.special (h : ℤ_[p]) (f : C(ℤ_[p], ℚ_[p])):
    ∀ s : ℕ, ∃ (t : ℕ) (ht : t ≠ 0), ∀ n : ℕ, ‖δ_[h]^[p ^ t + n] f 0‖ ≤ max (Finset.sup' (Finset.range (p^t - 1)) (Finset.nonempty_range_iff.mpr (Nat.sub_ne_zero_of_lt (Nat.one_lt_pow ht hp.out.one_lt))) (fun j : ℕ ↦ (p : ℝ)^(-1 : ℤ) * ‖δ_[h]^[j + 1 + n] f 0‖)) ((p : ℝ)^(-(s : ℤ))) := by
  have hf : ∀ s : ℕ, ∃ t : ℕ, t ≠ 0 ∧ ∀ (b a: ℤ_[p]), ‖a - b‖ ≤ p^(-(t : ℤ)) → ‖f a - f b‖ ≤ p^(-(s : ℤ)) := Padic.uniformContinuous_then_nonzero_norm_le_pow (CompactSpace.uniformContinuous_of_continuous f.continuous)
  have hf' : ∀ s : ℕ, ∃ t : ℕ, t ≠ 0 ∧ ∀ (x : ℤ_[p]),  ‖f (x • h + (p : ℤ_[p])^t • h) - f (x • h)‖ ≤ p^(-(s : ℤ)) := by
    intro s
    specialize hf s
    obtain ⟨t, ⟨ht', ht⟩⟩ := hf
    use t
    apply And.intro ht'
    intro x
    specialize ht (x • h) (x • h + p^t • h)
    simp_rw [smul_eq_mul, zpow_neg, zpow_natCast]
    simp_rw [smul_eq_mul, nsmul_eq_mul, Nat.cast_pow, add_sub_cancel_left, PadicInt.norm_mul, PadicInt.norm_pow, PadicInt.norm_p, inv_pow, zpow_neg, zpow_natCast] at ht
    apply ht
    rw [mul_le_iff_le_one_right]
    · exact PadicInt.norm_le_one h
    · simp only [inv_pos]
      apply pow_pos
      simp only [Nat.cast_pos]
      exact hp.out.pos

  intro s
  specialize hf' s
  obtain ⟨t, ⟨ht', ht⟩⟩ := hf'
  use t
  use ht'
  intro n

  have k := Padic.bojanic h f n t
  simp_rw [Nat.choose_self, one_smul, zero_add, ← Function.iterate_add_apply, ← Finset.sum_neg_distrib] at k

  have hpt : p^t - 1 ≠ 0 := by
    apply Nat.sub_ne_zero_of_lt
    calc
      _ < 2^t := by
        exact Nat.one_lt_pow ht' Nat.one_lt_two
      _ ≤ _ := by
        apply Nat.pow_le_pow_of_le_left hp.out.two_le

  have hpt' : Finset.Nonempty (Finset.range (p^t - 1)) := by
    simp only [Finset.nonempty_range_iff]
    exact hpt
  have hn' : Finset.Nonempty (Finset.range (n + 1)) := by
    simp_rw [Finset.nonempty_range_succ]

  calc
    _ ≤ max ‖∑ x ∈ Finset.range (p ^ t - 1), -((p ^ t).choose (x + 1) • δ_[h]^[x + 1 + n] f 0)‖ ‖∑ x ∈ Finset.range (n + 1), ((-1 : ℤ) ^ (n - x) * (n.choose x)) • (f (p ^ t • h + x • h) - f (x • h))‖ := by
      rw [k]
      apply padicNormE.nonarchimedean
    _ ≤ max (Finset.sup' (Finset.range (p^t - 1)) hpt' (fun j : ℕ ↦ ‖-((p ^ t).choose (j + 1) • δ_[h]^[j + 1 + n] f 0)‖)) (Finset.sup' (Finset.range (n + 1)) hn' (fun j : ℕ ↦ ‖((-1 : ℤ) ^ (n - j) * (n.choose j)) • (f (p ^ t • h + j • h) - f (j • h))‖)) := by
      apply max_le_max
      · apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonempty (Finset.Aesop.range_nonempty hpt)
        intro _ hi
        apply Finset.le_sup' _ hi
      · apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonempty
        apply Finset.Aesop.range_nonempty (Nat.add_one_ne_zero n)
        intro _ hi
        apply Finset.le_sup' _ hi
    _ ≤ max (Finset.sup' (Finset.range (p^t - 1)) hpt' (fun j : ℕ ↦ ‖(p ^ t).choose (j + 1) • δ_[h]^[j + 1 + n] f 0‖)) (Finset.sup' (Finset.range (n + 1)) hn' (fun j : ℕ ↦ ‖(n.choose j : ℚ_[p])‖ * ‖f (p ^ t • h + j • h) - f (j • h)‖)) := by
      apply max_le_max
      · simp_rw [norm_neg, le_refl]
      · simp only [Int.reduceNeg, zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast, padicNormE.mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, le_refl]
    _ ≤ max (Finset.sup' (Finset.range (p^t - 1)) hpt' (fun j : ℕ ↦ ‖(p ^ t).choose (j + 1) • δ_[h]^[j + 1 + n] f 0‖)) (Finset.sup' (Finset.range (n + 1)) hn' (fun j : ℕ ↦ ‖f (p ^ t • h + j • h) - f (j • h)‖)) := by
      apply max_le_max
      · simp_rw [le_refl]
      · simp_rw [Finset.sup'_le_iff]
        intro a ha
        calc
          _ ≤ 1 * ‖f (p ^ t • h + a • h) - f (a • h)‖ := by
            apply mul_le_mul_of_nonneg_right (padicNormE.norm_int_le_one _)
            simp only [norm_nonneg]
          _ = ‖f (p ^ t • h + a • h) - f (a • h)‖ := by
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
          _ ≤ (p : ℝ)^(-(1 : ℕ) : ℤ) * ‖δ_[h]^[a + 1 + n] f 0‖ := by
            apply mul_le_mul_of_nonneg_right
            · rw [padicNormE.norm_nat_le_pow_iff_dvd, pow_one]
              apply Nat.cast_dvd_cast
              apply Nat.Prime.dvd_choose_pow
              · exact hp.out
              . apply Nat.add_one_ne_zero
              · simp only [Finset.mem_range] at ha
                apply Nat.ne_of_lt
                rw[← Nat.lt_sub_iff_add_lt]
                exact ha
            · simp only [norm_nonneg]
          _ ≤ _ := by
            simp only [Nat.cast_one, le_refl]
      · simp only [Finset.sup'_le_iff]
        intro a _
        specialize ht a
        rw [add_comm]
        simp only [nsmul_eq_mul, Nat.cast_pow, zpow_neg, zpow_natCast]
        simp only [smul_eq_mul, zpow_neg, zpow_natCast] at ht
        exact ht

------------------------------------------------------------------------------------------

theorem PadicInt.fwdDiff_tendsto_zero (h : ℤ_[p]) (f : C(ℤ_[p], ℚ_[p])) :
    Filter.Tendsto (fun k ↦ δ_[h]^[k] f 0) Filter.atTop (nhds 0) := by
  ---
  simp only [Padic.tendsto_atTop_norm_le_pow, Rat.cast_zero, sub_zero]
  obtain ⟨y, hy'⟩ := ContinuousMap.exists_norm_eq_norm_apply f
  have hy := fun x ↦ ContinuousMap.norm_coe_le_norm f x
  rw [← hy'] at hy

  cases hb : Padic.addValuation (f y) with
  | top =>
    have k : f = (fun (_ : ℤ_[p]) ↦ (0 : ℚ_[p])) := by
      by_contra k
      have k' : ∃ x : ℤ_[p], f x ≠ 0 := by
        contrapose! k
        funext x
        apply k
      obtain ⟨x, hx⟩ := k'
      have l : Padic.addValuation (f x) = ⊤ := by
        ---
        rw [eq_top_iff, ← hb, Padic.addValuation_le_addValuation]
        apply hy
      have l' : Padic.addValuation (f x) ≠ ⊤ := by
        simp only [Padic.addValuation.apply hx, ne_eq, WithTop.coe_ne_top, not_false_eq_true]
      exact l' l
    rw [k]
    simp only [ge_iff_le, fwdDiff_const_zero_iter, norm_zero, zpow_neg, zpow_natCast, inv_nonneg, Nat.cast_nonneg, pow_nonneg, implies_true, exists_const]
  | coe b =>
    wlog hb' : b = 0
    · rw [← ne_eq] at hb'
      specialize this h ((p^(-b : ℤ) : ℚ_[p]) • f) y
      simp only [ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, padicNormE.mul, padicNormE.norm_p_zpow, zpow_natCast, neg_neg, norm_smul, hy', true_implies] at this
      have Hx : ∀ (x : ℤ_[p]), (p : ℝ)^b * ‖f x‖ ≤ (p : ℝ)^b * ‖f‖ := by
        intro x
        specialize hy x
        apply (mul_le_mul_iff_of_pos_left ?_).mpr
        · rw [← hy']
          exact hy
        · simp only [← Real.rpow_intCast]
          apply Real.rpow_pos_of_pos
          simp only [Nat.cast_pos]
          exact hp.out.pos
      specialize this Hx 0
      have Hb : Padic.addValuation ((p : ℚ_[p]) ^ (-b : ℤ) * f y) = (0 : ℤ) := by
        ---
        rw [eq_comm, Padic.eq_addValuation_iff_norm_eq_pow_neg]
        simp only [zpow_neg, padicNormE.mul, norm_inv, padicNormE.norm_p_zpow, inv_inv, neg_zero, zpow_zero]
        apply (IsUnit.mul_eq_one_iff_inv_eq _).mpr _
        · simp only [isUnit_iff_ne_zero]
          simp only [← Real.rpow_intCast]
          rw [Real.rpow_ne_zero]
          · simp only [ne_eq, Nat.cast_eq_zero]
            simp only [← ne_eq]
            exact hp.out.ne_zero
          · simp only [Nat.cast_nonneg]
          · simp only [ne_eq, Int.cast_eq_zero]
            simp only [← ne_eq]
            exact hb'
        · ---
          rw [← zpow_neg, eq_comm, ← Padic.eq_addValuation_iff_norm_eq_pow_neg, eq_comm]
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
        apply Real.rpow_pos_of_pos
        simp only [Nat.cast_pos]
        exact hp.out.pos
      rw [← (mul_le_mul_iff_of_pos_right Hp)]
      calc
        _ ≤ (p : ℝ)^(-(Nat.floor (m - b) : ℤ)) := by
          apply hN
        _ ≤ _ := by
          simp only [← Real.rpow_intCast]
          rw [← Real.rpow_add]
          rw [Real.rpow_le_rpow_left_iff]
          simp only [Nat.floor_int, Int.ofNat_toNat, Int.cast_neg, Int.cast_max, Int.cast_sub, Int.cast_natCast, Int.cast_zero, le_neg_add_iff_add_le, add_neg_le_iff_le_add]
          rw [add_comm]
          rw [← sub_le_iff_le_add]
          simp only [le_max_iff, le_refl, tsub_le_iff_right, zero_add, true_or]
          · simp only [Nat.one_lt_cast]
            exact hp.out.one_lt
          · simp only [Nat.cast_pos]
            exact hp.out.pos
    · rw [hb'] at hb
      have l := Padic.special h f
      have l' : ∀ s : ℕ, ∃ t : ℕ, t ≠ 0 ∧ ∀ j : ℕ, j ≤ s → ∀ n : ℕ, (j * p ^ t ≤ n → ‖δ_[h]^[n] f 0‖ ≤ (p : ℝ) ^ (- j : ℤ)) := by
        intro s
        specialize l s
        obtain ⟨t, ⟨ht', ht⟩⟩ := l
        use t
        apply And.intro ht'
        intro j
        induction' j with j hj
        . simp only [zero_mul, zero_le, CharP.cast_eq_zero, add_zero, true_implies]
          ---
          simp only [← Padic.le_addValuation]
          rw [← hb]
          ---
          simp only [Padic.addValuation_le_addValuation]
          rw [hy']
          apply IsUltrametricDist.norm_fwdDiff_iter_apply_le
        · intro hj' n hn
          specialize ht (n - p^t)
          have : p ^ t + (n - p ^ t) = n := by
            apply Nat.add_sub_of_le
            calc
              _ ≤ (j + 1) * p^t := by
                apply Nat.le_mul_of_pos_left (p ^ t)
                simp only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true]
              _ ≤ _ := hn
          simp only [this] at ht
          simp only [le_max_iff, Finset.le_sup'_iff] at ht
          specialize hj (le_of_lt (Nat.add_one_le_of_lt hj'))
          cases ht with
          | inl H =>
            obtain ⟨k, ⟨-, hk⟩⟩ := H
            have : j * p ^ t ≤ k + 1 + (n - p ^ t) := by
              apply le_add_left
              apply Nat.le_sub_of_add_le
              calc
                _ = (j + 1) * p ^ t := by
                  rw[add_mul, one_mul]
                _ ≤ _ := hn
            specialize hj (k + 1 + (n - p ^ t)) this
            calc
              _ ≤ (p : ℝ)^(-1 : ℤ) * ‖δ_[h]^[k + 1 + (n - p ^ t)] f 0‖ := hk
              _ ≤ (p : ℝ)^(-1 : ℤ) * (p : ℝ)^(-j : ℤ) := by
                apply (mul_le_mul_iff_of_pos_left ?_).mpr
                . exact hj
                · simp only [Int.reduceNeg, zpow_neg, zpow_one, inv_pos, Nat.cast_pos]
                  exact hp.out.pos
              _ = _ := by
                simp only [← Real.rpow_intCast]
                rw [← Real.rpow_add]
                simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one, Int.cast_natCast, Nat.cast_add, Nat.cast_one, neg_add_rev, Int.cast_add]
                · simp only [Nat.cast_pos]
                  exact hp.out.pos
          | inr H =>
            calc
              _ ≤ (p: ℝ)^(-s : ℤ) := H
              _ ≤ _ := by
                apply zpow_le_zpow_right₀
                · simp only [Nat.one_le_cast]
                  exact hp.out.one_le
                · apply Int.neg_le_neg
                  rw [Nat.cast_le]
                  exact hj'
      intro m
      specialize l' m
      obtain ⟨t, ⟨_, ht⟩⟩ := l'
      specialize ht m
      simp only [le_refl, true_implies] at ht
      use (m * p^t)

----------------------------------------------------------------------------------------------------------------------------------------------

theorem natural_mahler (f : C(ℤ_[p], ℚ_[p])) (n : ℕ) :
    f n = ∑' k : ℕ, δ_[1]^[k] f 0 / (k.factorial : ℚ_[p]) * (descPochhammer ℤ_[p] k).eval (n : ℤ_[p]) := by
  simp_rw [descPochhammer_eval_eq_descFactorial, PadicInt.coe_natCast, div_mul_comm]
  have (n : ℕ) :
      n = ((n : ℚ) : ℚ_[p]) := by
    simp only [Rat.cast_natCast]

  simp_rw [this, ← Padic.coe_div]

  have (n k : ℕ) :
      ((n.descFactorial k) : ℚ) / (k.factorial : ℚ) = n.choose k := by
    simp_rw [Nat.choose_eq_descFactorial_div_factorial]
    rw [Nat.cast_div]
    · exact Nat.factorial_dvd_descFactorial n k
    · simp_rw [ne_eq, Nat.cast_eq_zero, ← ne_eq]
      apply Nat.factorial_ne_zero

  simp_rw [this, Rat.cast_natCast]

  have (n : ℕ) : ∑' k : ℕ, (n.choose k) * δ_[1]^[k] f 0 = ∑ k ∈ Finset.range (n + 1), (n.choose k) * δ_[1]^[k] f 0 := by
    rw [tsum_eq_sum]
    intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    simp only [mul_eq_zero, Nat.cast_eq_zero]
    apply Or.intro_left
    rw [Nat.choose_eq_zero_iff]
    exact hk

  simp_rw [this]

  have := shift_eq_sum_fwdDiff_iter 1 f n 0
  simp only [nsmul_eq_mul, mul_one, zero_add] at this

  exact this

/-
theorem stupid : NonarchimedeanAddGroup ℤ_[p] := by
  exact IsUltrametricDist.nonarchimedeanAddGroup
-/

theorem PadicInt.norm_descPochhammer_le (k : ℕ) (x : ℤ_[p]) :
    ‖(descPochhammer ℤ_[p] k).eval x‖ ≤ ‖(k.factorial : ℚ_[p])‖ := by
  calc
    _ = ‖(-1)^k * (descPochhammer ℤ_[p] k).eval x‖ := by
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    _ = ‖(ascPochhammer ℤ_[p] k).eval (-x)‖ := by
      rw [← ascPochhammer_eval_neg_eq_descPochhammer]
    _ ≤ _ := norm_ascPochhammer_le _ _

theorem my_mahler (f : C(ℤ_[p], ℚ_[p])) :
    f = fun (x : ℤ_[p]) ↦ ∑' k : ℕ, δ_[1]^[k] f 0 / (k.factorial : ℚ_[p]) * (descPochhammer ℤ_[p] k).eval x := by
  apply DenseRange.equalizer PadicInt.denseRange_natCast (ContinuousMap.continuous f)
  · have : TendstoUniformly (fun n x ↦ ∑ k ∈ Finset.range (n + 1), δ_[1]^[k] f 0 / k.factorial * (Polynomial.eval x (descPochhammer ℤ_[p] k))) (fun x ↦ ∑' (k : ℕ), δ_[1]^[k] f 0 / k.factorial * (Polynomial.eval x (descPochhammer ℤ_[p] k))) Filter.atTop := by
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      simp_rw [Filter.eventually_atTop, ge_iff_le, dist_eq_norm_sub]
      use 0
      intro b hb x
      sorry
      /-
        rw [← Nat.cofinite_eq_atTop]
        rw [TendstoUniformly]

        Filter.Tendsto.cauchySeq
        cauchySeq_tendsto_of_isComplete


        rw [← tendstoUniformlyOn_univ, tendstoUniformly_iff_tendsto]
        rw [← tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace]
        rw [← ContinuousMap.tendsto_iff_tendstoLocallyUniformly]

        apply ContinuousMap.tendstoLocallyUniformly_of_tendsto
        apply Filter.Tendsto.cauchySeq

        apply Filter.Tendsto.tendstoUniformlyOn

        apply UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto
        · apply NonarchimedeanAddGroup.cauchySeq_sum_of_tendsto_cofinite_zero
          sorry
        · simp only [Set.mem_univ, forall_const]
          intro x
          sorry

        UniformCauchySeqOn.cauchy_map
        apply NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero
      -/
    apply TendstoUniformly.continuous this
    · simp only [Filter.eventually_atTop, ge_iff_le]
      use 0
      intro _ _
      apply continuous_finset_sum (Finset.range _)
      intro _ _
      exact Continuous.mul continuous_const (Continuous.comp' (Continuous.subtype_val continuous_id') (Polynomial.continuous_eval₂ _ _))
  · ext n
    simp_rw [Function.comp_apply, natural_mahler]
