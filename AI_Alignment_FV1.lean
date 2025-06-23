/-
Copyright (c) 2025 Li Jingyuan . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Li Jingyuan
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-
Let X be a nonempty finite set, Δ(X) = { p : X → [0, 1] | ∑_{x ∈ X} p(x) = 1},
and let ≿ denote a binary relation on Δ(X). As usual, ≻ and ∼ denote the
asymmetric and symmetric parts of ≿. In our nomenclature elements of X
are outcomes (or consequences or prizes), elements of Δ(X) are lotteries,
and ≿ is the preference relation.
-/

set_option autoImplicit false
set_option warningAsError false
set_option tactic.hygienic false
set_option linter.unusedVariables false


variable {X : Type} [Fintype X] [Nonempty X] [DecidableEq X]
variable (isCatastrophic : X → Prop)[DecidablePred isCatastrophic]

noncomputable instance : DecidableEq Real := Classical.decEq Real

def Lottery (X : Type) [Fintype X] := { p : X → Real // (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1 }

noncomputable instance : DecidableEq (Lottery X) := Classical.decEq (Lottery X)

namespace Lottery

/-- Convex combination of lotteries -/
def mix (p q : Lottery X) (α : Real) {hα_nonneg : 0 ≤ α} {hα_le_one : α ≤ 1} : Lottery X :=
  ⟨λ x => α * p.val x + (1 - α) * q.val x,
   by
     constructor
     · intro x
       have h₁ : 0 ≤ p.val x := p.property.1 x
       have h₂ : 0 ≤ q.val x := q.property.1 x
       -- hα_nonneg and hα_le_one are now parameters to the function
       have h₁_mult : 0 ≤ α * p.val x := mul_nonneg hα_nonneg h₁
       have h_one_minus_α : 0 ≤ 1 - α := by linarith
       have h₂_mult : 0 ≤ (1 - α) * q.val x := mul_nonneg h_one_minus_α h₂
       exact add_nonneg h₁_mult h₂_mult
     · calc
           ∑ x, (α * p.val x + (1 - α) * q.val x)
             = α * ∑ x, p.val x + (1 - α) * ∑ x, q.val x := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
             _ = α * 1 + (1 - α) * 1 := by rw [p.property.2, q.property.2]
             _ = 1 := by ring
    ⟩

/-- Check if a lottery is catastrophe-free (safe) -/
def isSafe (p : Lottery X) (isCatastrophic : X → Prop) : Prop :=
  ∀ x : X, p.val x > 0 → ¬isCatastrophic x

/-- Check if a lottery has a catastrophic outcome with positive probability -/
def hasRisk (p : Lottery X) (isCatastrophic : X → Prop) : Prop :=
  ∃ x : X, isCatastrophic x ∧ p.val x > 0

end Lottery

/-- Strict preference, derived from a preference relation -/
def strictPref {X : Type} [Fintype X] (pref : Lottery X → Lottery X → Prop)
               (p q : Lottery X) : Prop :=
  pref p q ∧ ¬(pref q p)

/-- Expected utility of a lottery given a utility function -/
def expectedUtility (p : Lottery X) (u : X → Real) : Real :=
  ∑ x, p.val x * u x

/-- Expected utility of a mixed lottery -/
lemma expectedUtility_mix {X : Type} [Fintype X] (p q : Lottery X) (u : X → Real) (α : Real)
  {hα_nonneg : 0 ≤ α} {hα_le_one : α ≤ 1} :
  expectedUtility (@Lottery.mix X _ p q α hα_nonneg hα_le_one) u =
  α * expectedUtility p u + (1 - α) * expectedUtility q u := by
  unfold expectedUtility
  simp only [Lottery.mix]
  calc ∑ x, (α * p.val x + (1 - α) * q.val x) * u x = α * (∑ x, p.val x * u x) + (1 - α) * (∑ x, q.val x * u x) := by {
    simp_rw [add_mul, Finset.sum_add_distrib, mul_assoc, Finset.mul_sum]
  }

/--
AI preference structure that aligns with human values and safety constraints.
-/
structure AlignedAIPreferences (X : Type) [Fintype X] [Nonempty X] [DecidableEq X] (isCatastrophic : X → Prop) where
  /-- AI preference relation -/
  pref : Lottery X → Lottery X → Prop
  /-- Human preference relation -/
  humanPref : Lottery X → Lottery X → Prop

  /-- Utility function representing the AI's preferences -/
  utilityFn : X → Real

  /-- The utility function represents the preference relation -/
  utility_representation : ∀ p q : Lottery X,
    pref p q ↔ expectedUtility p utilityFn ≥ expectedUtility q utilityFn

  /-- AI never prefers a lottery with catastrophic outcomes over a safe alternative -/
  safety_constraint : ∀ p q : Lottery X,
    Lottery.hasRisk p isCatastrophic →
    Lottery.isSafe q isCatastrophic →
    ¬(pref p q)

  /-- If p is safe and humans strictly prefer p over q, so must the AI -/
  safe_preference_alignment : ∀ p q : Lottery X,
    Lottery.isSafe p isCatastrophic →
    strictPref humanPref p q →
    strictPref pref p q

  /-- The deference principle: AI should adopt human's preference structure -/
  deference_principle : ∀ p q : Lottery X,
    (∀ r : Lottery X, humanPref q r → humanPref p r) →
    pref p q

  /-- Safety constraint ensures AI prefers safe lotteries over unsafe ones -/
  theorem safety_preference
      {X : Type} [Fintype X] [Nonempty X] [DecidableEq X]
      {isCatastrophic : X → Prop}
      (ai : AlignedAIPreferences X isCatastrophic)
      (p q : Lottery X)
      (h_p_unsafe : Lottery.hasRisk p isCatastrophic)
      (h_q_safe : Lottery.isSafe q isCatastrophic) :
      ai.pref q p := by
    -- The safety_constraint tells us ¬ai.pref p q
    have h_not_pref_pq := ai.safety_constraint p q h_p_unsafe h_q_safe

    -- Use utility representation to show q is preferred
    rw [ai.utility_representation]
    rw [ai.utility_representation] at h_not_pref_pq

    -- From ¬(EU(p) ≥ EU(q)), we get EU(p) < EU(q), hence EU(q) > EU(p)
    exact le_of_not_ge h_not_pref_pq

  /-- Strict AI preference implies strict utility inequality -/
  theorem strict_pref_utility_inequality
      {X : Type} [Fintype X] [Nonempty X] [DecidableEq X]
      {isCatastrophic : X → Prop} [DecidablePred isCatastrophic]
      (ai : AlignedAIPreferences X isCatastrophic)
      (p q : Lottery X)
      (h_strict : strictPref ai.pref p q) :
      expectedUtility p ai.utilityFn > expectedUtility q ai.utilityFn := by
    -- Extract the components of strict preference
    obtain ⟨h_pref_pq, h_not_pref_qp⟩ := h_strict

    -- From p ≽ q, we get EU(p) ≥ EU(q)
    rw [ai.utility_representation] at h_pref_pq

    -- From ¬(q ≽ p), we get ¬(EU(q) ≥ EU(p))
    rw [ai.utility_representation] at h_not_pref_qp
    push_neg at h_not_pref_qp

    -- Combine to get strict inequality
    exact h_not_pref_qp

  /-- Dominance principle: if p dominates q in human preferences, AI prefers p to q -/
  theorem dominance_principle
      {X : Type} [Fintype X] [Nonempty X] [DecidableEq X]
      {isCatastrophic : X → Prop}
      (ai : AlignedAIPreferences X isCatastrophic)
      (p q : Lottery X)
      (h_strict_dominance : (∀ r : Lottery X, ai.humanPref q r → ai.humanPref p r) ∧
                           (∃ r : Lottery X, ai.humanPref p r ∧ ¬ai.humanPref q r)) :
      ai.pref p q := by
    -- Extract the dominance relationship
    obtain ⟨h_dominance, _⟩ := h_strict_dominance

    -- Apply the deference principle directly
    exact ai.deference_principle p q h_dominance

  /-- The alignment compatibility theorem for safe lotteries -/
  theorem alignment_compatibility
      {X : Type} [Fintype X] [Nonempty X] [DecidableEq X]
      {isCatastrophic : X → Prop}
      (ai : AlignedAIPreferences X isCatastrophic)
      (h_human_complete : ∀ p q : Lottery X, ai.humanPref p q ∨ ai.humanPref q p)
      (h_human_transitive : ∀ p q r : Lottery X,
                  ai.humanPref p q → ai.humanPref q r → ai.humanPref p r) :
    ∀ p q : Lottery X,
        Lottery.isSafe p isCatastrophic →
        strictPref ai.humanPref p q →
        strictPref ai.pref p q := by
    intros p q h_p_safe h_human_strict_pref
    -- For safe lotteries, we can use safe_preference_alignment directly
    exact ai.safe_preference_alignment p q h_p_safe h_human_strict_pref


theorem alignment_impossibility
    {X : Type} [Fintype X] [Nonempty X] [DecidableEq X]
    (isCatastrophic : X → Prop) [DecidablePred isCatastrophic]
    (humanPref : Lottery X → Lottery X → Prop)
    (p : Lottery X) (h_p_unsafe : Lottery.hasRisk p isCatastrophic)
    (h_exists_safe : ∃ q : Lottery X, Lottery.isSafe q isCatastrophic)
    (h_humans_prefer_unsafe : ∀ q, Lottery.isSafe q isCatastrophic →
                                      strictPref humanPref p q) :
    ¬∃ aiPref : Lottery X → Lottery X → Prop,
      (∀ p' q', strictPref humanPref p' q' → strictPref aiPref p' q') ∧
      (∀ p' q', Lottery.hasRisk p' isCatastrophic → Lottery.isSafe q' isCatastrophic →
                ¬aiPref p' q') := by
  intro h_exists_aiPref
  obtain ⟨aiPref, h_full_align, h_safety⟩ := h_exists_aiPref
  obtain ⟨q, h_q_safe⟩ := h_exists_safe

  -- Human strict preference of p over q
  have h_human_pref_p_q := h_humans_prefer_unsafe q h_q_safe

  -- By full alignment, AI must also prefer p to q
  have h_ai_pref_p_q := h_full_align p q h_human_pref_p_q

  -- But this contradicts the safety constraint
  have h_not_ai_pref_p_q := h_safety p q h_p_unsafe h_q_safe
  exact h_not_ai_pref_p_q h_ai_pref_p_q.1
