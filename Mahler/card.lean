import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open MeasureTheory
open ProbabilityMeasure

inductive Color where
  | red : Color
  | black : Color
  deriving Repr

inductive Suit where
  | spades : Suit
  | hearts : Suit
  | diamonds : Suit
  | clubs : Suit
  deriving Repr

def color_of (s : Suit) : Color := match s with
  | Suit.spades => Color.black
  | Suit.hearts => Color.red
  | Suit.diamonds => Color.red
  | Suit.clubs => Color.black

structure Card where
  suit : Suit
  rank : ℕ
  deriving Repr

def Card.create (suit : Suit) (rank : ℕ) : Card :=
  Card.mk suit (if rank % 13 = 0 then 13 else (rank % 13))

def Card.color (card : Card) : Color :=
  color_of card.suit

def Card.is_red (card : Card) : Bool :=
  match card.color with
  | Color.red => True
  | Color.black => False

instance Card.instNonempty : Nonempty Card :=
  exists_true_iff_nonempty.mp ⟨Card.create Suit.spades 4, trivial⟩

instance Card.instFintype : Fintype Card := by
  sorry

instance Card.instMeasurableSpace : MeasurableSpace Card := by
  sorry

instance Card.MeasurableSingletonClass : MeasurableSingletonClass Card := by
  sorry

-- Finset.instMembership

-- PMF.uniformOfFinset
-- PMF.integral_eq_sum
noncomputable def ℙ := PMF.uniformOfFintype Card

example : ∫ x : Card, (Bool.toNat x.is_red : ℝ) ∂ℙ.toMeasure = 26 := by
  sorry
