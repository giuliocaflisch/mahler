import Mathlib

-- CURRY-HOWARD CORRESPONDENCE
-- ___________________________

-- • Propositions as Types

def x : ℕ := 1

def P : Prop := 0 = 0 + 0
def p : P := rfl

-- • Logical Connectives as Simple Types

-- Implication

example (P : Prop) : P → P := fun p ↦ p
example (P Q : Prop) (p : P) (p_implies_q : P → Q) : Q := p_implies_q p

-- Disjunction

example (P Q : Prop) (p : P) : P ∨ Q := Or.inl p
example (P Q : Prop) (q : Q) : P ∨ Q := Or.inr q

-- Conjunction

example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := ⟨p, q⟩

-- • Logical Quantifiers as Dependent Types

-- Existence
-- (I don't like proof irrelevance)

def proof_1 : ∃ x : ℕ, 0 < x := ⟨1, zero_lt_one⟩
def proof_2 : ∃ x : ℕ, 0 < x := ⟨2, zero_lt_two⟩

#eval proof_1 = proof_2

-- Universality

example : ∀ x : ℕ, 0 + x = x := fun x ↦ zero_add x
