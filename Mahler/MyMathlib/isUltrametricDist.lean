import Mahler.MyMathlib.ForwardDiff

import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.ContinuousMap.Compact

variable {G M : Type*} [AddCommMonoid M] [AddCommGroup G] (h : M)

theorem IsUltrametricDist.norm_fwdDiff_iter_apply_le {M G : Type*} [TopologicalSpace M] [CompactSpace M] [AddCommMonoid M] [SeminormedAddCommGroup G] [IsUltrametricDist G]
    (h : M) (f : C(M, G)) (m : M) (n : ℕ) : ‖δ_[h]^[n] f m‖ ≤ ‖f‖ := by
  rw [fwdDiff_iter_eq_sum_shift]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonempty (Finset.nonempty_range_iff.mpr (Nat.add_one_ne_zero _))
  intro _ _
  exact le_trans (norm_zsmul_le _ _) (ContinuousMap.norm_coe_le_norm _ _)
