import Mathlib.MeasureTheory.MeasurableSpace.Defs

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Notation
import Mathlib.Probability.ProbabilityMassFunction.Integrals

import Mathlib.Order.Interval.Finset.Defs

import Mathlib.Tactic.DeriveFintype

import Mathlib.Algebra.Group.Indicator

import Init.Data.List.Basic

open MeasureTheory
open ProbabilityTheory

def Rank := { n : ℕ // n ∈ (Finset.Icc 1 13)} deriving Repr, Fintype, DecidableEq, MeasurableSpace

instance Rank.instCoeNat : Coe Rank Nat := ⟨Subtype.val⟩

instance Rank.instNonempty : Nonempty Rank := by
  rw[Rank]
  simp only [Finset.mem_Icc, nonempty_subtype]
  use 1
  simp only [le_refl, Nat.one_le_ofNat, and_self]


inductive Color where
  | red : Color
  | black : Color
  deriving Repr, Fintype, Nonempty, DecidableEq

instance Color.instMeasurableSpace : MeasurableSpace Color := ⊤

inductive Suit where
  | spades : Suit
  | hearts : Suit
  | diamonds : Suit
  | clubs : Suit
  deriving Repr, Fintype, Nonempty, DecidableEq

instance Suit.instMeasurableSpace : MeasurableSpace Color := ⊤

def Suit.color (s: Suit) : Color := match s with
  | Suit.spades => Color.black
  | Suit.hearts => Color.red
  | Suit.diamonds => Color.red
  | Suit.clubs => Color.black


structure Card where
  suit: Suit
  rank: Rank
  deriving Repr, Fintype, Nonempty, DecidableEq

instance Card.instMeasurableSpace : MeasurableSpace Card := ⊤

def Card.color (card : Card) : Color :=
  card.suit.color

noncomputable def prob_card : PMF Card := PMF.uniformOfFintype Card

noncomputable def prob_measure_card : Measure Card := prob_card.toMeasure

def all_suseets_of_tot_cards (n : ℕ) := {x : Finset Card // x.card = n}



def Card.isred (card : Card) : Bool := match card.color with
  | Color.red => true
  | _ => false

def indicator (b : Bool) : ℕ := match b with
  | true => 1
  | _ => 0

theorem Card.has52instances : Fintype.card Card = 52 := rfl

def deck : Finset Card := {x : Card | True}
def deck_red : Finset Card := {x : Card | x.color = Color.red}

theorem deck_red.has26Instances : deck_red.card = 26 := by
  exact rfl

noncomputable def indicator_card_isred (card : Card) : ℝ :=
  (deck_red : Set Card).indicator (fun _ ↦ (1: ℝ)) card

theorem very_basic_deck : ∫ (c : Card), indicator_card_isred c ∂prob_measure_card = 1/2 := by
  simp_rw[prob_measure_card]
  rw[PMF.integral_eq_sum]
  simp_rw[prob_card]
  simp_rw[PMF.uniformOfFintype_apply]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_nat, smul_eq_mul, mul_comm]
  rw[← Finset.sum_mul]
  simp_rw[Card.has52instances]
  rw[one_div]
  rw[← eq_div_iff, div_inv_eq_mul, inv_mul_eq_div]
  · simp_rw[indicator_card_isred]
    rw[Finset.sum_indicator_eq_sum_inter]
    simp only [Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw[deck_red.has26Instances]
    rw [eq_div_iff]
    · nth_rw 2 [← Nat.cast_ofNat]
      rw [← Nat.cast_mul]
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
  · simp only [Nat.cast_ofNat, ne_eq, inv_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true]

noncomputable instance : MeasureSpace Card where
  __ := (show MeasurableSpace Card from inferInstance)
  volume := prob_measure_card

example : prob_measure_card[indicator_card_isred] = 1/2 := by
  apply very_basic_deck

example : 𝔼[indicator_card_isred] = 1/2 := by exact very_basic_deck

instance deck_red.instMeasurableSet : MeasurableSet (deck_red : Set Card) := trivial

example : prob_measure_card deck_red = 1/2 := by
  rw [← Nat.cast_one, ← Nat.cast_two]
  rw [prob_measure_card, prob_card, PMF.toMeasure_uniformOfFintype_apply]
  simp_rw [Finset.coe_sort_coe, Fintype.card_coe]
  rw [deck_red.has26Instances, Card.has52instances]
  simp_rw [← ENNReal.coe_natCast]
  repeat rw [← ENNReal.coe_div]
  have stupid : ((26 : ℕ) : NNReal) / ((52 : ℕ) : NNReal) = ((1 : ℕ) : NNReal) / ((2 : ℕ) : NNReal) := by
    rw [div_eq_div_iff]
    · repeat rw [← Nat.cast_mul]
    · simp_rw [Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    · simp_rw [Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
  simp_rw [stupid]
  · simp_rw [Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
  · simp_rw [Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
  · exact deck_red.instMeasurableSet

-------------------------------------------------------------------------------

def Nat_leq_52 := {n : ℕ // n ∈ Finset.Icc 0 (Fintype.card Card)} deriving Repr, Fintype, DecidableEq, MeasurableSpace

instance Nat_leq_52.instNonempty : Nonempty Nat_leq_52 := by
  rw [Nat_leq_52]
  simp only [Finset.mem_Icc, nonempty_subtype]
  use 1
  simp only [zero_le, true_and]
  exact NeZero.one_le

instance Nat_leq_52.instCoeNat : Coe Nat_leq_52 Nat := ⟨Subtype.val⟩

def all_subsets_of_n_card (n : Nat_leq_52) := {X : Finset Card // X.card = n}

instance all_subsets_of_n_card.instFintype (n : Nat_leq_52) : Fintype (all_subsets_of_n_card n) := by
  rw [all_subsets_of_n_card]
  exact Subtype.fintype _


noncomputable def generate_arbitrary_subset_of_deck (n : Nat_leq_52) : Finset Card :=
  let deck_list : List Card := deck.toList
  let x := List.take n deck_list
  let y := (Multiset.ofList x).toFinset
  y

/-
instance all_subsets_of_n_card.instNonempty (n : Nat_leq_52) : Nonempty (all_subsets_of_n_card n) := by
  rw [all_subsets_of_n_card]
  rw [nonempty_subtype]
  use (generate_arbitrary_subset_of_deck n)
  rw [generate_arbitrary_subset_of_deck]
  simp only [List.toFinset_coe]
  rw [deck]
  simp only [Finset.filter_True]
  sorry

def generate_arbitrary_subset_of_deck2 (n : Nat_leq_52) : Finset Card :=
  let decide_suit (n : Nat_leq_52) : Suit :=
    match (n : ℕ) / 13 with
    | 0 => Suit.spades
    | 1 => Suit.hearts
    | 2 => Suit.diamonds
    | _ => Suit.clubs
  let decide_rank (n : Nat_leq_52) : Rank :=
    (n : ℕ) % 13
  let m : ℕ := n
  match m with
    | 0 => {x: Card | False}
    | _ => {Card.mk (decide_suit n) (decide_rank n)} ∪ {generate_arbitrary_subset_of_deck2 (n - 1)}

def prob_measure_subsets_of_n_card (n : ℕ) := PMF.uniformOfFintype (all_subsets_of_n_card n)
-/
