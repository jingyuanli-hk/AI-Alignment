/-
Copyright (c) 2025 Li Jingyuan . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Li Jingyuan
-/
import Mathlib.Order.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp


/-
This file defines and proves the uniqueness theorem for von Neumann-Morgenstern
utility representation.
-/
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

end Lottery

/-- Preference relation on lotteries -/
class PrefRel (X : Type) [Fintype X] [Nonempty X] where
  /-- The preference relation (≿) -/
  pref : Lottery X → Lottery X → Prop
  /-- A1: Completeness and transitivity -/
  complete : ∀ p q : Lottery X, pref p q ∨ pref q p
  transitive : ∀ p q r : Lottery X, pref p q → pref q r → pref p r
  /-- A2: Continuity -/
  continuity : ∀ p q r : Lottery X, pref p q → pref q r → ¬(pref r p) →
                ∃ α β : Real, ∃ h_conj : 0 < α ∧ α < 1 ∧ 0 < β ∧ β < 1,
                pref (@Lottery.mix X _ p r α (le_of_lt h_conj.1) (le_of_lt h_conj.2.1)) q ∧
                ¬(pref q (@Lottery.mix X _ p r α (le_of_lt h_conj.1) (le_of_lt h_conj.2.1))) ∧
                pref q (@Lottery.mix X _ p r β (le_of_lt h_conj.2.2.1) (le_of_lt h_conj.2.2.2)) ∧
                ¬(pref (@Lottery.mix X _ p r β (le_of_lt h_conj.2.2.1) (le_of_lt h_conj.2.2.2)) q)
  /-- A3: Independence or substitution -/
  independence : ∀ p q r : Lottery X, ∀ α : Real, (h_α_cond : 0 < α ∧ α ≤ 1) →
                 (pref p q ∧ ¬(pref q p)) →
                 (pref (@Lottery.mix X _ p r α (le_of_lt h_α_cond.1) h_α_cond.2) (@Lottery.mix X _ q r α (le_of_lt h_α_cond.1) h_α_cond.2) ∧
                  ¬(pref (@Lottery.mix X _ q r α (le_of_lt h_α_cond.1) h_α_cond.2) (@Lottery.mix X _ p r α (le_of_lt h_α_cond.1) h_α_cond.2)))
  /-- A3b: Independence for indifference -/
  indep_indiff : ∀ p q r : Lottery X, ∀ α : Real, (h_α_cond : 0 < α ∧ α ≤ 1) →
                 (pref p q ∧ pref q p) → (pref (@Lottery.mix X _ p r α (le_of_lt h_α_cond.1) h_α_cond.2) (@Lottery.mix X _ q r α (le_of_lt h_α_cond.1) h_α_cond.2) ∧ pref (@Lottery.mix X _ q r α (le_of_lt h_α_cond.1) h_α_cond.2) (@Lottery.mix X _ p r α (le_of_lt h_α_cond.1) h_α_cond.2))

variable [PrefRel X]

instance : IsTrans (Lottery X) PrefRel.pref :=
  ⟨PrefRel.transitive⟩

instance : IsTotal (Lottery X) PrefRel.pref :=
  ⟨PrefRel.complete⟩

/-- Strict preference: p ≻ q -/
def strictPref (p q : Lottery X) : Prop := PrefRel.pref p q ∧ ¬(PrefRel.pref q p)

/-- Indifference: p ~ q -/
def indiff (p q : Lottery X) : Prop := PrefRel.pref p q ∧ PrefRel.pref q p

notation:50 p " ≿ " q => PrefRel.pref p q
notation:50 p " ≻ " q => strictPref p q
notation:50 p " ~ " q => indiff p q

/-- Expected utility of a lottery given a utility function -/
def expectedUtility (p : Lottery X) (u : X → Real) : Real :=
  ∑ x, p.val x * u x

/-- Theorem 6.2 (Utility Uniqueness): This theorem establishes that if two utility functions represent the same preference relation on lotteries, then one utility function must be a positive affine transformation of the other.

Significance: This result is foundational in expected utility theory, as it ensures that the representation of preferences by utility functions is unique up to a positive affine transformation. This implies that the preference ordering is invariant under such transformations, preserving the consistency of decision-making.

Assumptions:
1. The preference relation satisfies the axioms of completeness, transitivity, continuity, and independence.
2. The utility functions represent the same preference relation, meaning they assign the same ordering to lotteries.

Implications: The theorem guarantees that the utility representation is robust and consistent, allowing for meaningful comparisons of preferences across different contexts. It also highlights the structural properties of utility functions in capturing preferences accurately.
    then one must be a positive affine transformation of the other -/
theorem utility_uniqueness {u v : X → Real}
  (h_u : ∀ p q : Lottery X, PrefRel.pref p q ↔ expectedUtility p u ≥ expectedUtility q u)
  (h_v : ∀ p q : Lottery X, PrefRel.pref p q ↔ expectedUtility p v ≥ expectedUtility q v) :
  ∃ (α β : Real), α > 0 ∧ (∀ x : X, v x = α * u x + β) := by

  -- Define degenerate lotteries
  let δ : X → Lottery X := fun x_val =>
    ⟨fun y => if y = x_val then 1 else 0, by
      constructor
      · intro y; by_cases h : y = x_val <;> simp [h]
      · simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]⟩

  -- Cache extreme outcomes according to u
  let ⟨x_max, _, h_u_max⟩ := Finset.exists_max_image Finset.univ u Finset.univ_nonempty
  let ⟨x_min, _, h_u_min⟩ := Finset.exists_min_image Finset.univ u Finset.univ_nonempty
  by_cases h_u_constant : ∀ x, u x = u x_min
  case pos =>
    -- Case 1: u is constant
    have h_indiff : ∀ p q : Lottery X, p ~ q := by
      intro p q
      have h_EU_eq : expectedUtility p u = expectedUtility q u := by
        calc expectedUtility p u
            = ∑ x, p.val x * u x := rfl
            _ = ∑ x, p.val x * u x_min := by
                congr
                ext x
                rw [h_u_constant x]
            _ = u x_min * ∑ x, p.val x := by
                rw [Finset.mul_sum]
                congr
                ext x
                rw [mul_comm]
            _ = u x_min * 1 := by rw [p.property.2]
            _ = u x_min := by rw [mul_one]
            _ = u x_min * 1 := by rw [mul_one]
            _ = u x_min * ∑ x, q.val x := by rw [q.property.2]
            _ = ∑ x, q.val x * u x_min := by
                rw [Finset.mul_sum]
                congr
                ext x
                rw [mul_comm]
            _ = ∑ x, q.val x * u x := by
                congr
                ext x
                rw [h_u_constant x]
            _ = expectedUtility q u := rfl

      -- Since u represents preference and expected utilities are equal,
      -- p and q are indifferent
      have h_p_prefers_q : p ≿ q := by
        rw [h_u p q]
        rw [h_EU_eq]

      have h_q_prefers_p : q ≿ p := by
        rw [h_u q p]
        rw [h_EU_eq]

      exact ⟨h_p_prefers_q, h_q_prefers_p⟩

    -- Since all lotteries are indifferent, v must be constant
    have h_v_constant : ∀ x y, v x = v y := by
      intro x y
      let p := δ x
      let q := δ y

      -- By indifference, p ~ q
      have h_p_indiff_q := h_indiff p q

      -- Use v representation
      have h_EU_v_eq : expectedUtility p v = expectedUtility q v := by
        apply le_antisymm
        · -- Goal: expectedUtility p v ≤ expectedUtility q v
          -- This is equivalent to expectedUtility q v ≥ expectedUtility p v
          -- We have h_p_indiff_q.2 : q ≿ p
          -- And h_v q p : (q ≿ p) ↔ (expectedUtility q v ≥ expectedUtility p v)
          -- So, (h_v q p).mp h_p_indiff_q.2 gives the desired result.
          exact (h_v q p).mp h_p_indiff_q.2
        · -- Goal: expectedUtility q v ≤ expectedUtility p v
          -- This is equivalent to expectedUtility p v ≥ expectedUtility q v
          -- We have h_p_indiff_q.1 : p ≿ q
          -- And h_v p q : (p ≿ q) ↔ (expectedUtility p v ≥ expectedUtility q v)
          -- So, (h_v p q).mp h_p_indiff_q.1 gives the desired result.
          exact (h_v p q).mp h_p_indiff_q.1

      -- For degenerate lotteries, expected utility equals utility
      calc v x
          = ∑ z, p.val z * v z := by
              simp [p, δ, expectedUtility]
          _ = expectedUtility p v := rfl
          _ = expectedUtility q v := h_EU_v_eq
          _ = ∑ z, q.val z * v z := rfl
          _ = v y := by
              simp [q, δ, expectedUtility]

    -- Now construct the affine relationship
    let α : Real := 1  -- α = 1 > 0
    let β := v x_min - u x_min * α

    use α, β
    constructor
    · exact zero_lt_one
    · intro x
      have h_v_eq_constant : v x = v x_min := h_v_constant x x_min
      have h_u_eq_constant : u x = u x_min := h_u_constant x

      -- Calculate the affine relationship

      calc v x = v x_min := h_v_eq_constant
      _ = v x_min - u x_min + u x_min := by ring
      _ = v x_min - u x_min * 1 + u x_min * 1 := by ring
      _ = (v x_min - u x_min * 1) + 1 * u x_min := by ring
      _ = β + α * u x_min := by rfl
      _ = β + α * u x := by rw [h_u_eq_constant]
      _ = α * u x + β := by ring

  case neg =>
    -- Case 2: u is not constant
    -- There exists x such that u x ≠ u x_min
  · -- There exists x such that u x ≠ u x_min
    push_neg at h_u_constant
    let x_diff := Classical.choose h_u_constant
    have h_x_diff : u x_diff ≠ u x_min := Classical.choose_spec h_u_constant

    -- After `push_neg at h_u_constant` (line 232), h_u_constant is (∃ x, u x ≠ u x_min),
    -- which is captured by h_some_diff.
    -- We use x_diff and h_x_diff (derived from h_some_diff) to show u x_diff > u x_min.
    have h_x_diff_gt : u x_diff > u x_min := by
      have h_ge := h_u_min x_diff (Finset.mem_univ x_diff)
      exact lt_of_le_of_ne h_ge (Ne.symm h_x_diff)

    -- Since u is not constant, u x_max > u x_min
    have h_max_gt_min : u x_max > u x_min := by
      have h_ge := h_u_min x_max
      by_contra h_eq
      push_neg at h_eq
      have h_eq' : u x_max = u x_min := le_antisymm h_eq (h_ge (Finset.mem_univ x_max))
      -- Contradiction with non-constant u
      have h_contradiction : ∀ x, u x = u x_min := by
        intro x
        have h_x_le_max := h_u_max x (Finset.mem_univ x)
        have h_min_le_x := h_u_min x (Finset.mem_univ x)
        -- If u x_min = u x_max and u x_min ≤ u x ≤ u x_max, then u x = u x_min
        rw [h_eq'] at h_x_le_max
        exact le_antisymm h_x_le_max h_min_le_x
      -- h_u_constant is ∃ x, u x ≠ u x_min (from the outer scope, after push_neg)
      -- h_contradiction is ∀ x, u x = u x_min
      -- These are contradictory.
      obtain ⟨x_witness, h_witness_neq⟩ := h_u_constant
      have h_witness_eq := h_contradiction x_witness
      exact h_witness_neq h_witness_eq

    -- Define best and worst lotteries
    let p_best := δ x_max
    let p_worst := δ x_min

    -- p_best ≻ p_worst (strict preference)
    have h_best_succ_worst : p_best ≻ p_worst := by
      constructor
      · -- p_best ≿ p_worst
        rw [h_u p_best p_worst]
        simp [expectedUtility, p_best, p_worst, δ]
        exact le_of_lt h_max_gt_min
      · -- ¬(p_worst ≿ p_best)
        rw [h_u p_worst p_best]
        simp [expectedUtility, p_best, p_worst, δ]
        exact h_max_gt_min

    -- For any α ∈ [0, 1], define lottery mix_α = α·p_best + (1-α)·p_worst
    let mix (α : Real) (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1) : Lottery X :=
      @Lottery.mix X _ p_best p_worst α hα_nonneg hα_le_one -- Explicitly pass hα_nonneg and hα_le_one

    -- Expected utility of mix_α under u is a linear function of α
    have h_mix_EU_u : ∀ α (h_α : α ∈ Set.Icc 0 1), expectedUtility (mix α h_α.1 h_α.2) u =
                                         u x_min + α * (u x_max - u x_min) := by
      intro α h_α
      simp [expectedUtility, mix, Lottery.mix]
      -- Calculate expected utility
      -- Expand the sum by manually rewriting
      simp_rw [add_mul] -- Distribute u x over the sum: ∑ (A+B)*C  =>  ∑ (A*C + B*C)
      rw [Finset.sum_add_distrib] -- Distribute sum over addition: ∑ (X+Y) => ∑ X + ∑ Y
      simp_rw [mul_assoc] -- Rearrange products for Finset.mul_sum: (c*P)*U => c*(P*U)
      rw [← Finset.mul_sum, ← Finset.mul_sum] -- Factor out α and (1-α): ∑ (c*Q) => c * ∑ Q
      -- Use properties of p_best and p_worst
      have h_p_best : ∀ x, p_best.val x = if x = x_max then 1 else 0 := by
        intro x; by_cases h : x = x_max <;> simp [h, p_best, δ]
      have h_p_worst : ∀ x, p_worst.val x = if x = x_min then 1 else 0 := by
        intro x; by_cases h : x = x_min <;> simp [h, p_worst, δ]
      -- Substitute and simplify
      calc α * ∑ i, p_best.val i * u i + (1 - α) * ∑ i, p_worst.val i * u i
          = α * u x_max + (1 - α) * u x_min := by
              -- Simplify the sums using the properties of p_best and p_worst
              have h_sum_best : ∑ i, p_best.val i * u i = u x_max := by
                simp only [p_best, δ, expectedUtility]
                simp_rw [ite_mul, zero_mul, one_mul]
                rw [Finset.sum_ite_eq' Finset.univ x_max u]
                simp -- This will simplify (if x_max ∈ Finset.univ then u x_max else 0) to u x_max
              have h_sum_worst : ∑ i, p_worst.val i * u i = u x_min := by
                simp only [p_worst, δ, expectedUtility]
                simp_rw [ite_mul, zero_mul, one_mul]
                rw [Finset.sum_ite_eq' Finset.univ x_min u]
                simp -- This will simplify (if x_min ∈ Finset.univ then u x_min else 0) to u x_min
              rw [h_sum_best, h_sum_worst]
          _ = u x_min + α * (u x_max - u x_min) := by ring

    -- Similarly, expected utility under v is a linear function of α
    have h_mix_EU_v : ∀ α (h_α : α ∈ Set.Icc 0 1), expectedUtility (mix α h_α.1 h_α.2) v =
                                         v x_min + α * (v x_max - v x_min) := by
      intro α h_α
      simp [expectedUtility, mix, Lottery.mix] -- LHS becomes ∑ x, (α * p_best.val x + (1-α) * p_worst.val x) * v x
      simp_rw [add_mul]                       -- LHS becomes ∑ x, (α * p_best.val x * v x + (1-α) * p_worst.val x * v x)
      simp_rw [mul_assoc]                     -- LHS becomes ∑ x, (α * (p_best.val x * v x) + (1-α) * (p_worst.val x * v x))
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] -- LHS becomes α * (∑ x, p_best.val x * v x) + (1-α) * (∑ x, p_worst.val x * v x)

      have h_sum_best_v : ∑ i, p_best.val i * v i = v x_max := by
        simp only [p_best, δ]
        simp_rw [ite_mul, zero_mul, one_mul]
        rw [Finset.sum_ite_eq' Finset.univ x_max v]
        simp
      have h_sum_worst_v : ∑ i, p_worst.val i * v i = v x_min := by
        simp only [p_worst, δ]
        simp_rw [ite_mul, zero_mul, one_mul]
        rw [Finset.sum_ite_eq' Finset.univ x_min v]
        simp
      rw [h_sum_best_v, h_sum_worst_v] -- Goal: α * v x_max + (1 - α) * v x_min = v x_min + α * (v x_max - v x_min)
      ring

    -- For each x, we can find α such that δ_x ~ mix α
    -- Using Claim V from the vNM theorem
    -- Since u represents preferences, there exists α_x such that:
    -- expectedUtility (δ x) u = expectedUtility (mix α_x) u
    have h_exists_α : ∀ x, ∃ (α : Real) (h_α : α ∈ Set.Icc 0 1), expectedUtility (δ x) u =
                                              expectedUtility (mix α h_α.1 h_α.2) u := by
      intro x
      -- Calculate expected utility of δ_x under u
      have h_EU_δ_u : expectedUtility (δ x) u = u x := by
        simp only [expectedUtility, δ]
        simp_rw [ite_mul, zero_mul, one_mul]
        rw [Finset.sum_ite_eq' Finset.univ x u]
        simp -- to handle the `if x ∈ Finset.univ then u x else 0`

      -- Find α such that u x = u x_min + α * (u x_max - u x_min)
      let α_x := (u x - u x_min) / (u x_max - u x_min)

      -- Check α_x ∈ [0, 1]
      have h_α_x_nonneg : 0 ≤ α_x := by
        apply div_nonneg
        · exact sub_nonneg.mpr (h_u_min x (Finset.mem_univ x))
        · exact le_of_lt (sub_pos.mpr h_max_gt_min)
      have h_α_x_le_one : α_x ≤ 1 := by
        apply div_le_one_of_le₀
        · -- Numerator ≤ Denominator
          -- Goal: u x - u x_min ≤ u x_max - u x_min
          apply sub_le_sub_right
          exact h_u_max x (Finset.mem_univ x) -- u x ≤ u x_max
        · exact le_of_lt (sub_pos.mpr h_max_gt_min) -- Denominator is positive

      -- Check expected utility equality
      have h_EU_mix_α_u : expectedUtility (mix α_x h_α_x_nonneg h_α_x_le_one) u = u x := by
        rw [h_mix_EU_u α_x ⟨h_α_x_nonneg, h_α_x_le_one⟩]
        -- Goal: u x_min + α_x * (u x_max - u x_min) = u x
        -- where α_x = (u x - u x_min) / (u x_max - u x_min)
        simp only [α_x]
        have h_cancel : (u x - u x_min) / (u x_max - u x_min) * (u x_max - u x_min) = u x - u x_min := by
          apply div_mul_cancel₀
          exact sub_ne_zero.mpr (ne_of_gt h_max_gt_min)
        rw [h_cancel]
        ring

      use α_x, ⟨h_α_x_nonneg, h_α_x_le_one⟩
      rw [h_EU_δ_u, h_EU_mix_α_u]

    -- Since both u and v represent preferences, for each x:
    -- If δ_x ~ mix α_x, then:
    -- expectedUtility (δ x) v = expectedUtility (mix α_x) v
    have h_eq_EU_v : ∀ x, ∀ α (h_α : α ∈ Set.Icc 0 1), expectedUtility (δ x) u = expectedUtility (mix α h_α.1 h_α.2) u →
                                           expectedUtility (δ x) v = expectedUtility (mix α h_α.1 h_α.2) v := by
      intro x α h_α h_eq_u
      -- Since u represents preferences: δ_x ~ mix α
      have h_indiff : δ x ~ mix α h_α.1 h_α.2 := by
        constructor
        · rw [h_u (δ x) (mix α h_α.1 h_α.2)]
          rw [h_eq_u]
        · rw [h_u (mix α h_α.1 h_α.2) (δ x)]
          rw [h_eq_u]

      -- Since v also represents preferences
      have h_v_eq : expectedUtility (δ x) v = expectedUtility (mix α h_α.1 h_α.2) v := by
        apply le_antisymm
        · -- Use h_v to show mix α ≿ δ x implies expectedUtility (mix α) v ≥ expectedUtility (δ x) v
          have h2 : (mix α h_α.1 h_α.2 ≿ δ x) ↔ expectedUtility (mix α h_α.1 h_α.2) v ≥ expectedUtility (δ x) v := h_v (mix α h_α.1 h_α.2) (δ x)
          exact h2.mp h_indiff.2
        · -- Use h_v to show δ x ≿ mix α implies expectedUtility (δ x) v ≥ expectedUtility (mix α) v
          have h1 : (δ x ≿ mix α h_α.1 h_α.2) ↔ expectedUtility (δ x) v ≥ expectedUtility (mix α h_α.1 h_α.2) v := h_v (δ x) (mix α h_α.1 h_α.2)
          exact h1.mp h_indiff.1
      exact h_v_eq

    -- Where α_x = (u x - u x_min) / (u x_max - u x_min)
    -- For each x, we have:
    -- v x = v x_min + α_x * (v x_max - v x_min)
    -- u x = u x_min + α_x * (u x_max - u x_min)
    -- Where α_x = (u x - u x_min) / (u x_max - u x_min)
    -- Substituting, we get:
    -- v x = v x_min + [(u x - u x_min) / (u x_max - u x_min)] * (v x_max - v x_min)

    -- α is chosen as the ratio of the differences in utilities between v and u for the extreme outcomes.
    -- This ensures that the scaling factor aligns the differences proportionally, establishing the affine relationship.
    -- β represents the constant term in the affine transformation v(x) = α * u(x) + β,
    -- ensuring that the transformation aligns v(x_min) with α * u(x_min) + β.
    -- α represents the scaling factor that aligns the differences in utilities between v and u for the extreme outcomes.
    -- It ensures that the proportional differences are preserved, establishing the affine relationship.
    let α := (v x_max - v x_min) / (u x_max - u x_min)

    -- β represents the constant term in the affine transformation v(x) = α * u(x) + β.
    -- It ensures that the transformation aligns v(x_min) with α * u(x_min) + β.
    let β := v x_min - α * u x_min

    -- Check α > 0
    have h_α_pos : α > 0 := by
      -- Since p_best ≻ p_worst, we have v x_max > v x_min
      have h_v_max_gt_min : v x_max > v x_min := by
        -- By representation of v
        have h_best_pref_worst : p_best ≿ p_worst := h_best_succ_worst.1
        have h_worst_not_pref_best : ¬(p_worst ≿ p_best) := h_best_succ_worst.2

        -- Use the fact that v represents preferences
        rw [h_v p_best p_worst] at h_best_pref_worst
        rw [h_v p_worst p_best] at h_worst_not_pref_best

        -- Simplify expected utilities for degenerate lotteries
        have h_EU_best_v : expectedUtility p_best v = v x_max := by
          simp [expectedUtility, p_best, δ]
        have h_EU_worst_v : expectedUtility p_worst v = v x_min := by
          simp [expectedUtility, p_worst, δ]

        rw [h_EU_best_v, h_EU_worst_v] at h_best_pref_worst h_worst_not_pref_best

        -- From h_best_pref_worst we have v x_max ≥ v x_min
        -- From h_worst_not_pref_best we have ¬(v x_min ≥ v x_max)
        -- Together, these imply v x_max > v x_min
        exact lt_iff_le_not_le.mpr ⟨h_best_pref_worst, h_worst_not_pref_best⟩

      -- Now prove α > 0
      exact div_pos
        (sub_pos.mpr h_v_max_gt_min)
        (sub_pos.mpr h_max_gt_min)

    -- β is defined as v x_min - α * u x_min
    -- Now prove v x = α * u x + β for all x
    use α, β
    constructor
    · exact h_α_pos
    · intro x
      -- Get α_x such that δ_x ~ mix α_x
      obtain ⟨α_x, h_α_x, h_EU_eq⟩ := h_exists_α x

      -- Calculate v x
      have h_v_x : v x = expectedUtility (δ x) v := by
        simp only [expectedUtility, δ] -- Goal: v x = ∑ i, (if i = x then 1 else 0) * v i
        simp_rw [ite_mul, zero_mul, one_mul]
        rw [Finset.sum_ite_eq' Finset.univ x v]
        rw [if_pos (Finset.mem_univ x)] -- Goal: v x = v x

      -- Derive affine relationship
      have h_denom_ne_zero : u x_max - u x_min ≠ 0 := sub_ne_zero.mpr (ne_of_gt h_max_gt_min)

      -- Establish the value of α_x from h_exists_α and h_EU_eq
      have h_α_x_val_eq : α_x = (u x - u x_min) / (u x_max - u x_min) := by
        have h_lhs_u_expand : expectedUtility (δ x) u = u x := by
          simp only [expectedUtility, δ, ite_mul, zero_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        have h_rhs_u_expand : expectedUtility (mix α_x h_α_x.1 h_α_x.2) u =
               u x_min + α_x * (u x_max - u x_min) :=
          h_mix_EU_u α_x h_α_x
        have h_ux_eq_expanded_mix : u x = u x_min + α_x * (u x_max - u x_min) := by
          rw [h_lhs_u_expand, h_rhs_u_expand] at h_EU_eq
          exact h_EU_eq
        -- Solve for α_x: u x = u x_min + α_x * (u x_max - u x_min)
        -- => u x - u x_min = α_x * (u x_max - u x_min)
        -- => (u x - u x_min) / (u x_max - u x_min) = α_x
        rw [eq_div_iff h_denom_ne_zero] -- Target: α_x * (u x_max - u x_min) = u x - u x_min
        rw [eq_sub_iff_add_eq] -- Target: u x = u x_min + α_x * (u x_max - u x_min)
        rw [eq_comm]
        rw [add_comm]
        exact h_ux_eq_expanded_mix

      -- We know that v x = v x_min + α_x * (v x_max - v x_min)
      -- where α_x = (u x - u x_min) / (u x_max - u x_min)

      -- First, use h_eq_EU_v to get the relationship for v
      have h_v_x_eq : v x = v x_min + α_x * (v x_max - v x_min) := by
        -- Apply h_eq_EU_v with the α_x we found
        have h_v_eq_mix : expectedUtility (δ x) v = expectedUtility (mix α_x h_α_x.1 h_α_x.2) v :=
          h_eq_EU_v x α_x h_α_x h_EU_eq

        -- Simplify LHS
        have h_lhs : expectedUtility (δ x) v = v x := by
          simp only [expectedUtility, δ, ite_mul, zero_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

        -- Simplify RHS using h_mix_EU_v
        have h_rhs : expectedUtility (mix α_x h_α_x.1 h_α_x.2) v = v x_min + α_x * (v x_max - v x_min) :=
          h_mix_EU_v α_x h_α_x

        rw [h_lhs, h_rhs] at h_v_eq_mix
        exact h_v_eq_mix
      -- Expand the expression for α and β
      simp only [α, β]

      -- Substitute α = (v x_max - v x_min) / (u x_max - u x_min)
      -- and β = v x_min - α * u x_min into the equation.
      -- We need to show: v x = α * u x + β
      -- From h_v_x_eq: v x = v x_min + α_x * (v x_max - v x_min)
      -- From h_α_x_val_eq: α_x = (u x - u x_min) / (u x_max - u x_min)

      rw [h_v_x_eq, h_α_x_val_eq]
      -- Goal: v x_min + (u x - u x_min) / (u x_max - u x_min) * (v x_max - v x_min) =
      --       (v x_max - v x_min) / (u x_max - u x_min) * u x + (v x_min - (v x_max - v x_min) / (u x_max - u x_min) * u x_min)

      -- Clear denominators and simplify
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
      ring_nf
