import Mathlib.MeasureTheory.MeasurableSpace.Defs

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Notation

import Mathlib.Order.Interval.Finset.Defs

import Mathlib.Tactic.DeriveFintype

import Mathlib.Algebra.Group.Indicator

open MeasureTheory
open ProbabilityTheory

inductive Color where
  | red : Color
  | black : Color
  deriving Repr, Fintype, Nonempty, DecidableEq

instance Color.instMeasurableSpace : MeasurableSpace Color := ⊤

inductive Suit where
  | hearts : Suit
  | diamonds : Suit
  | spades : Suit
  | clubs : Suit
  deriving Repr, Fintype, Nonempty, DecidableEq

instance Suit.instMeasurableSpace : MeasurableSpace Suit := ⊤

def Suit.color (s : Suit) : Color :=
  match s with
  | Suit.hearts => Color.red
  | Suit.diamonds => Color.red
  | Suit.spades => Color.black
  | Suit.clubs => Color.black

def Rank := { n : ℕ // n ∈ Finset.Icc 1 13} deriving Repr, Fintype, DecidableEq, MeasurableSpace

instance Rank.instNonempty : Nonempty Rank := by
  rw [Rank]
  simp_rw [Finset.mem_Icc, nonempty_subtype]
  use 1
  simp_rw [le_refl, Nat.one_le_ofNat, and_self]

structure Card where
  suit : Suit
  rank : Rank
  deriving Repr, Fintype, Nonempty, DecidableEq

def Card.color (card : Card) : Color :=
  card.suit.color

def Card.is_red (card : Card) : Bool :=
  match card.color with
  | Color.red => true
  | _ => false

instance Card.instMeasurableSpace : MeasurableSpace Card := ⊤

theorem Card.has52Instances : Fintype.card Card = 52 := rfl

-----------------------------------------------------------------------------

noncomputable def p := PMF.uniformOfFintype Card

noncomputable def P := p.toMeasure

def deck : Finset Card := {x : Card | True}
def deck_red : Finset Card := {x : Card | x.color = Color.red}

theorem deck_red.has26Instances : deck_red.card = 26 := rfl

noncomputable def indicator_card_isred (c : Card) := (deck_red : Set Card).indicator (fun _ ↦ (1 : ℝ)) c

example : ∫ c, indicator_card_isred c ∂P = 1 / 2 := by
  rw [P, p]
  rw [PMF.integral_eq_sum]
  simp_rw [PMF.uniformOfFintype_apply]
  simp_rw [smul_eq_mul]
  simp_rw [ENNReal.toReal_inv, ENNReal.toReal_nat, one_div]
  simp_rw [mul_comm]
  simp_rw [← Finset.sum_mul]
  simp_rw [Card.has52Instances]
  rw [← eq_div_iff]
  rw [div_inv_eq_mul]
  rw [inv_mul_eq_div]
  · simp_rw [indicator_card_isred]
    rw [Finset.sum_indicator_eq_sum_inter]
    simp_rw [Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [deck_red.has26Instances]
    rw [eq_div_iff]
    · rw [← Nat.cast_two, ← Nat.cast_mul]
    · simp_rw [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
  · simp_rw [Nat.cast_ofNat, ne_eq, inv_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true]

-----------------------------------------------------------------------------
