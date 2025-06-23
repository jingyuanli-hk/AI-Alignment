/-
Copyright (c) 2025 Li Jingyuan . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Li Jingyuan
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real.Lemmas


/-
Let X be a nonempty finite set, Δ(X) = { p : X → [0, 1] | ∑_{x ∈ X} p(x) = 1},
and let ≿ denote a binary relation on Δ(X). As usual, ≻ and ∼ denote the
asymmetric and symmetric parts of ≿. In our nomenclature elements of X
are outcomes (or consequences or prizes), elements of Δ(X) are lotteries,
and ≿ is the preference relation.
-/

set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedVariables false


variable {X : Type} [Fintype X] [Nonempty X] [DecidableEq X]

noncomputable instance : DecidableEq Real := Classical.decEq Real

def Lottery (X : Type) [Fintype X] := { p : X → Real // (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1 }

noncomputable instance : DecidableEq (Lottery X) := Classical.decEq (Lottery X)

namespace Lottery

/--Proposition 3.3 Convex combination of lotteries -/
def mix (p q : Lottery X) (α : Real) {hα_nonneg : 0 ≤ α} {hα_le_one : α ≤ 1} : Lottery X :=
  ⟨λ x => α * p.val x + (1 - α) * q.val x,
   by
     constructor
     · intro x
       have h₁ : 0 ≤ p.val x := p.property.1 x
       have h₂ : 0 ≤ q.val x := q.property.1 x
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
  { trans := fun p q r h₁ h₂ => PrefRel.transitive p q r h₁ h₂ }

/-- The `IsTotal` instance for `PrefRel.pref` ensures that the preference relation is total,
    meaning that for any two lotteries `p` and `q`, either `p ≿ q` or `q ≿ p` holds.
    This is a key property required for the von Neumann-Morgenstern utility theorem. -/
instance : IsTotal (Lottery X) PrefRel.pref :=
  ⟨PrefRel.complete⟩

/-- Strict preference: p ≻ q -/
def strictPref (p q : Lottery X) : Prop := PrefRel.pref p q ∧ ¬(PrefRel.pref q p)

/-- Indifference: p ~ q -/
def indiff (p q : Lottery X) : Prop := PrefRel.pref p q ∧ PrefRel.pref q p

notation:50 p " ≿ " q => PrefRel.pref p q
notation:50 p " ≻ " q => strictPref p q
notation:50 p " ~ " q => indiff p q

--Lemma 4.6 Properties of Preference Relations

omit [DecidableEq X] in
lemma strictPref_trans {p q r : Lottery X} (h₁ : p ≻ q) (h₂ : q ≻ r) : p ≻ r := by
  unfold strictPref at *
  constructor
  · exact PrefRel.transitive p q r h₁.1 h₂.1
  · intro hrp
    exact h₂.2 (PrefRel.transitive r p q hrp h₁.1)

instance : IsTrans (Lottery X) strictPref :=
  ⟨fun p q r h₁ h₂ => strictPref_trans h₁ h₂⟩

omit [DecidableEq X] in
lemma PrefRel.refl (p : Lottery X) : p ≿ p :=
  (PrefRel.complete p p).elim id id

instance : IsIrrefl (Lottery X) strictPref :=
  ⟨fun p h => h.2 (PrefRel.refl p)⟩

-- Transitivity for p ~ q1, q1 ~ q2 => p ~ q2
omit [DecidableEq X] in
lemma PrefRel.transitive_indiff {p q1 q2 : Lottery X} (h1 : p ~ q1) (h2 : q1 ~ q2) : p ~ q2 :=
  ⟨PrefRel.transitive p q1 q2 h1.1 h2.1, PrefRel.transitive q2 q1 p h2.2 h1.2⟩
/-
Theorem (for lotteries). A binary relation ≿ on Δ(X) satisfies A1, A2,
and A3 if and only if there exists a (utility) function u : X → ℝ such that,

p ≿ q ⟺ ∑_{x ∈ X} p(x)u(x) ≥ ∑_{x ∈ X} q(x)u(x)

Moreover, a function v : X → ℝ satisfies

p ≿ q ⟺ ∑_{x ∈ X} p(x)v(x) ≥ ∑_{x ∈ X} q(x)v(x)

if and only if v(x) = αu(x) + β on X for some α, β ∈ ℝ, α > 0.
-/

/-- Expected utility of a lottery given utility function u -/
noncomputable def expectedUtility (p : Lottery X) (u : X → Real) : Real :=
  ∑ x ∈ Finset.filter (fun x => p.val x ≠ 0) Finset.univ, p.val x * u x

omit [DecidableEq X]

/-- Claim 5.1: p ≻ q, 0 < α < 1 imply p ≻ αp + (1-α)q ≻ q -/
theorem claim_i {p q : Lottery X} (h : p ≻ q) (α : Real) (hα : 0 < α) (hα₂ : α < 1) :
  (p ≻ @Lottery.mix X _ p q α (le_of_lt hα) (le_of_lt hα₂)) ∧ (@Lottery.mix X _ p q α (le_of_lt hα) (le_of_lt hα₂) ≻ q) := by
  constructor
  · unfold strictPref
    constructor
    · -- Show p ≿ p.mix q α
      have h₃ : (1 - α) > 0 := by linarith
      have h_cond : 0 < 1 - α ∧ 1 - α ≤ 1 := ⟨h₃, by linarith⟩
      have h_use_indep := PrefRel.independence p q p (1 - α) h_cond h

      have h_mix_p_p : @Lottery.mix X _ p p (1 - α) (le_of_lt h₃) h_cond.2 = p := by
        apply Subtype.eq
        ext x
        simp [Lottery.mix]
        have h_sum_to_one : (1 - α) + α = 1 := by ring
        calc (1 - α) * p.val x + α * p.val x = ((1 - α) + α) * p.val x := by ring
             _ = 1 * p.val x := by rw [h_sum_to_one]
             _ = p.val x := by simp

      have h_mix_q_p_comm : @Lottery.mix X _ q p (1 - α) (le_of_lt h₃) (sub_le_self 1 (le_of_lt hα)) = @Lottery.mix X _ p q α (le_of_lt hα) (le_of_lt hα₂) := by
        apply Subtype.eq
        ext x
        simp [Lottery.mix]
        ring

      rw [h_mix_p_p, h_mix_q_p_comm] at h_use_indep
      exact h_use_indep.1
    · -- Show ¬(p.mix q α ≿ p)
      have h₃ : (1 - α) > 0 := by linarith
      have h_cond : 0 < 1 - α ∧ 1 - α ≤ 1 := ⟨h₃, by linarith⟩
      have h_use_indep := PrefRel.independence p q p (1 - α) h_cond h

      have h_mix_p_p : @Lottery.mix X _ p p (1 - α) (le_of_lt h₃) h_cond.2 = p := by
        apply Subtype.eq
        ext x
        simp [Lottery.mix]
        have h_sum_to_one : (1 - α) + α = 1 := by ring
        calc (1 - α) * p.val x + α * p.val x = ((1 - α) + α) * p.val x := by ring
             _ = 1 * p.val x := by rw [h_sum_to_one]
             _ = p.val x := by simp

      have h_mix_q_p_comm : @Lottery.mix X _ q p (1 - α) (le_of_lt h₃) (sub_le_self 1 (le_of_lt hα)) = @Lottery.mix X _ p q α (le_of_lt hα) (le_of_lt hα₂) := by
        apply Subtype.eq
        ext x
        simp [Lottery.mix]
        ring

      rw [h_mix_p_p, h_mix_q_p_comm] at h_use_indep
      -- After rewriting, h_use_indep.2 gives us exactly what we need: ¬(mix p q α ≿ p)
      exact h_use_indep.2
  · -- We need to prove that αp + (1-α)q ≻ q, which means:
    -- 1. αp + (1-α)q ≿ q
    -- 2. ¬(q ≿ αp + (1-α)q)
    -- We can use independence axiom (A3) with r = q

    -- First, let's establish that mix q q α = q
    have h_mix_q_q : @Lottery.mix X _ q q α (le_of_lt hα) (le_of_lt hα₂) = q := by
      apply Subtype.eq
      ext x
      simp [Lottery.mix]
      -- α*q(x) + (1-α)*q(x) = q(x)
      ring

    -- Now apply independence axiom
    have h_use_indep := PrefRel.independence p q q α ⟨hα, le_of_lt hα₂⟩ h
    rw [h_mix_q_q] at h_use_indep

    -- This gives us exactly what we need
    exact ⟨h_use_indep.1, h_use_indep.2⟩

/-- Claim 5.2: p ≻ q, 0 ≤ α < β ≤ 1 imply βp + (1-β)q ≻ αp + (1-α)q -/
theorem claim_ii {p q : Lottery X} (α β : Real) (h : p ≻ q) (hα : 0 ≤ α) (hαβ : α < β) (hβ : β ≤ 1) :
  let hβ_nonneg : 0 ≤ β := le_trans hα (le_of_lt hαβ)
  let hα_le_one : α ≤ 1 := le_trans (le_of_lt hαβ) hβ
  @Lottery.mix X _ p q β hβ_nonneg hβ ≻ @Lottery.mix X _ p q α hα hα_le_one := by

  -- Define these inside the proof body to make them available to nested blocks
  have hβ_nonneg : 0 ≤ β := le_trans hα (le_of_lt hαβ)
  have hα_le_one : α ≤ 1 := le_trans (le_of_lt hαβ) hβ

  by_cases hα₀ : α = 0
  · by_cases hβ₁ : β = 1
    · subst hα₀; subst hβ₁
      -- If α = 0 and β = 1, then βp + (1-β)q = p and αp + (1-α)q = q
      -- So we need to show p ≻ q, which is given
      -- First let's simplify the lottery mixtures
      have hp : @Lottery.mix X _ p q 1 hβ_nonneg hβ = p := by
        apply Subtype.eq
        ext x
        simp [Lottery.mix]  -- 1*p(x) + (1-1)*q(x) = p(x)

      have hq : @Lottery.mix X _ p q 0 hα hα_le_one = q := by
        apply Subtype.eq
        ext x
        simp [Lottery.mix]  -- 0*p(x) + (1-0)*q(x) = q(x)

      -- Now prove p ≻ q using the definition of strictPref
      unfold strictPref
      constructor
      · rw [hp, hq]
        exact h.1
      · rw [hp, hq]
        exact h.2
    · subst hα₀
      -- If α = 0 and β < 1, then αp + (1-α)q = q
      -- First simplify Lottery.mix p q 0 to q
      have hq : @Lottery.mix X _ p q 0 hα hα_le_one = q := by
        apply Subtype.eq
        ext x
        simp [Lottery.mix]  -- 0*p(x) + (1-0)*q(x) = q(x)

      -- We need to show Lottery.mix p q β ≻ q
      have hβ_pos : 0 < β := by linarith
      have hβ_lt_one : β < 1 := lt_of_le_of_ne hβ hβ₁

      -- By claim_i, we have p ≻ Lottery.mix p q β ≻ q
      have h_claim := claim_i h β hβ_pos hβ_lt_one

      -- The second part gives us exactly what we need
      have h_goal : @Lottery.mix X _ p q β hβ_nonneg hβ ≻ @Lottery.mix X _ p q 0 (by linarith) (by linarith) := by
        rw [hq]
        exact h_claim.2
      exact h_goal

  · by_cases hβ₁ : β = 1
    · -- Case where 0 < α and β = 1
      subst hβ₁  -- β = 1
      -- When β = 1, we have βp + (1-β)q = p
      have hp : @Lottery.mix X _ p q 1 hβ_nonneg hβ = p := by
        apply Subtype.eq
        ext x
        simp [Lottery.mix]  -- 1*p(x) + (1-1)*q(x) = p(x)

      -- We know α > 0 (from negation of hα₀) and α < 1 (from α < β = 1)
      have hα_pos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα₀)
      have hα_lt1 : α < 1 := by linarith

      -- Apply claim_i to get p ≻ αp + (1-α)q
      have h_claim := claim_i h α hα_pos hα_lt1

      -- The goal is to show Lottery.mix p q 1 ≻ Lottery.mix p q α
      simp only [hp]
      exact h_claim.1
    · -- Case where 0 < α < β < 1
      have hα₀' : 0 < α := lt_of_le_of_ne hα (Ne.symm hα₀)
      have hβ₁' : β < 1 := lt_of_le_of_ne hβ (Ne.intro hβ₁)
      -- By claim_i, p ≻ βp + (1-β)q ≻ q
      have h₁ : (p ≻ @Lottery.mix X _ p q β hβ_nonneg hβ) ∧ (@Lottery.mix X _ p q β hβ_nonneg hβ ≻ q) := claim_i h β (lt_trans hα₀' hαβ) hβ₁'
      -- Express αp + (1-α)q as convex combination of βp + (1-β)q and q
      have hγ : 0 < α/β ∧ α/β < 1 := by
        constructor
        · have hβ_pos : 0 < β := lt_trans hα₀' hαβ
          exact div_pos hα₀' hβ_pos
        · have hβpos : 0 < β := lt_trans hα₀' hαβ
          have h_div : α/β < β/β := by
            rw [div_lt_div_iff_of_pos_right hβpos]
            exact hαβ
          rw [div_self (ne_of_gt hβpos)] at h_div
          exact h_div
      -- αp + (1-α)q = (α/β)·(βp + (1-β)q) + (1-α/β)·q
      -- Express αp + (1-α)q as (α/β)(βp + (1-β)q) + (1-α/β)q
      let γ := α/β
      have h_mix_αβ : @Lottery.mix X _ p q α hα hα_le_one =
        @Lottery.mix X _ (@Lottery.mix X _ p q β hβ_nonneg hβ) q γ (le_of_lt hγ.1) (le_of_lt hγ.2) := by {
        apply Subtype.eq
        ext x
        simp [Lottery.mix]
        have h_βpos : β > 0 := lt_trans hα₀' hαβ
        calc α * p.val x + (1 - α) * q.val x
             = γ * (β * p.val x + (1 - β) * q.val x) + (1 - γ) * q.val x := by {
               -- Expand γ
               have h_γ_def : γ = α/β := by rfl
               rw [h_γ_def]
               -- Distribute
               rw [mul_add]
               -- (α/β) * (β * p.val x) = α * p.val x
               have h_mul_div : α/β * β = α := by
                 field_simp [ne_of_gt h_βpos]
               have h_term1 : α/β * (β * p.val x) = α * p.val x := by
                 rw [← mul_assoc, h_mul_div]
               rw [h_term1]
               -- Simplify the q.val x terms
               have h_q_terms : (α/β) * ((1 - β) * q.val x) + (1 - α/β) * q.val x = (1 - α) * q.val x := by {
                 -- Use a combination of targeted rewriting steps to prove this equality
                 have h1 : (α/β) * ((1 - β) * q.val x) = (α * (1 - β))/β * q.val x := by {
                     -- Use div_mul_eq_mul_div to rewrite (a/b)*c as (a*c)/b
                     rw [div_mul_eq_mul_div]
                     -- Apply associativity of multiplication
                     rw [←mul_assoc]
                     -- Simplify the division
                     field_simp [ne_of_gt h_βpos]
                 }

                 have h2 : 1 - α/β = (β - α)/β := by
                   field_simp [ne_of_gt h_βpos]

                 rw [h1, h2]

                 have h3 : (α * (1 - β))/β * q.val x + (β - α)/β * q.val x = ((α * (1 - β)) + (β - α))/β * q.val x := by {
                   rw [← add_mul]
                   rw [add_div]
                 }

                 rw [h3]

                 have h4 : (α * (1 - β)) + (β - α) = β * (1 - α) := by
                   ring

                 rw [h4]

                 have h5 : (β * (1 - α))/β * q.val x = (1 - α) * q.val x := by
                   field_simp [ne_of_gt h_βpos]

                 exact h5
               }
               rw [← h_q_terms]
               -- Fix associativity issue with ring
               ring
             }
      }

      -- Now use claim_i with h₁.2: βp + (1-β)q ≻ q
      have h_claim := claim_i h₁.2 γ hγ.1 hγ.2
      -- This gives us (βp + (1-β)q) ≻ γ(βp + (1-β)q) + (1-γ)q
      have h_goal : @Lottery.mix X _ p q β hβ_nonneg hβ ≻ @Lottery.mix X _ p q α hα hα_le_one := by
        rw [h_mix_αβ]
        exact h_claim.1
      exact h_goal

/-- Helper Lemma 5.2 for the first part of claim_iii: p ~ q implies p ~ αp + (1-α)q -/
lemma claim_iii_part1 {p q : Lottery X} (α : Real) (h : p ~ q) (hα₁ : 0 < α) (hα₂ : α < 1) :
  p ~ @Lottery.mix X _ p q α (le_of_lt hα₁) (le_of_lt hα₂) := by
  -- We want to show p ~ (αp + (1-α)q)
  -- Use PrefRel.indep_indiff with P' = p, Q' = q, R' = p, α_ax = 1-α
  -- indep_indiff states: P' ~ Q' → mix P' R' α_ax ~ mix Q' R' α_ax
  -- So: p ~ q → mix p p (1-α) ~ mix q p (1-α)
  have h_1_minus_α_pos : 0 < 1 - α := by linarith
  have h_1_minus_α_le_1 : 1 - α ≤ 1 := by linarith -- True since α > 0 implies 1-α < 1; α < 1 implies 1-α > 0.
  have h_cond_1_minus_α : 0 < 1 - α ∧ 1 - α ≤ 1 := ⟨h_1_minus_α_pos, h_1_minus_α_le_1⟩

  have h_indep_res := PrefRel.indep_indiff p q p (1-α) h_cond_1_minus_α h

  -- Now simplify the terms in h_indep_res: mix p p (1-α) ~ mix q p (1-α)
  -- First, mix p p (1-α) = p
  have h_mix_p_p_id : @Lottery.mix X _ p p (1 - α) (le_of_lt h_1_minus_α_pos) h_1_minus_α_le_1 = p := by
    apply Subtype.eq; ext x; simp [Lottery.mix]; ring
  rw [h_mix_p_p_id] at h_indep_res -- h_indep_res is now: p ~ mix q p (1-α)

  -- Second, mix q p (1-α) = (1-α)q + αp = αp + (1-α)q = mix p q α
  have h_mix_q_p_1_minus_α_eq_mix_p_q_α :
    @Lottery.mix X _ q p (1 - α) (le_of_lt h_1_minus_α_pos) (sub_le_self 1 (le_of_lt hα₁)) =
    @Lottery.mix X _ p q α (le_of_lt hα₁) (le_of_lt hα₂) := by
    apply Subtype.eq; ext x; simp [Lottery.mix]; ring
  rw [h_mix_q_p_1_minus_α_eq_mix_p_q_α] at h_indep_res -- h_indep_res is now: p ~ mix p q α
  exact h_indep_res

/-- Helper Lemma 5.3 for the second part of claim_iii: p ~ q implies αp + (1-α)q ~ q -/
lemma claim_iii_part2 {p q : Lottery X} (α : Real) (h : p ~ q) (hα₁ : 0 < α) (hα₂ : α < 1) :
  @Lottery.mix X _ p q α (le_of_lt hα₁) (le_of_lt hα₂) ~ q := by
  -- We want to show (αp + (1-α)q) ~ q
  -- Use PrefRel.indep_indiff with P' = p, Q' = q, R' = q, α_ax = α
  have h_α_cond : 0 < α ∧ α ≤ 1 := ⟨hα₁, le_of_lt hα₂⟩
  have h_indep_res := PrefRel.indep_indiff p q q α h_α_cond h
  -- h_indep_res is: mix p q α ~ mix q q α

  -- Simplify mix q q α = q
  have h_mix_q_q_id : @Lottery.mix X _ q q α (le_of_lt hα₁) (le_of_lt hα₂) = q := by
    apply Subtype.eq; ext x; simp [Lottery.mix]; ring

  rw [h_mix_q_q_id] at h_indep_res
  -- h_indep_res is now: mix p q α ~ q
  exact h_indep_res

/-- Claim 5.3: p ~ q, α ∈ (0, 1) imply p ~ αp + (1-α)q ~ q -/
theorem claim_iii {p q : Lottery X} (α : Real) (h : p ~ q) (hα₁ : 0 < α) (hα₂ : α < 1) :
  (p ~ @Lottery.mix X _ p q α (le_of_lt hα₁) (le_of_lt hα₂)) ∧ (@Lottery.mix X _ p q α
  (le_of_lt hα₁) (le_of_lt hα₂) ~ q) := by
    apply And.intro
    · exact claim_iii_part1 α h hα₁ hα₂
    · exact claim_iii_part2 α h hα₁ hα₂

/-- Claim 5.4: p ~ q, α ∈ (0, 1) imply αp + (1-α)r ~ αq + (1-α)r -/
theorem claim_iv {p q r : Lottery X} (α : Real) (h : p ~ q) (hα₁ : 0 < α) (hα₂ : α < 1) :
  @Lottery.mix X _ p r α (le_of_lt hα₁) (le_of_lt hα₂) ~ @Lottery.mix X _ q r α (le_of_lt hα₁) (le_of_lt hα₂) := by
  have h_α_cond : 0 < α ∧ α ≤ 1 := ⟨hα₁, le_of_lt hα₂⟩
  exact PrefRel.indep_indiff p q r α h_α_cond h

/-- Claim 5.5: If p ≿ q ≿ r and p ≻ r, then there exists a unique α* ∈ [0, 1]
    such that the lottery α*p + (1-α)r is indifferent to q. This unique α* represents
    the mixing probability that balances the lotteries, a crucial step in establishing
    the von Neumann-Morgenstern utility theorem. -/
 --   such that, α*p + (1-α*)r ~ q -/
theorem claim_v {p q r : Lottery X} (h₁ : p ≿ q) (h₂ : q ≿ r) (h₃ : p ≻ r) :
  ∃! α : ↥(Set.Icc (0:Real) 1), @Lottery.mix X _ p r α.val α.property.1 α.property.2 ~ q := by
  -- Define the set S = {α ∈ [0, 1] | αp + (1-α)r ≻ q}
  let S := {α_val : Real | ∃ (h_α_bounds : 0 ≤ α_val ∧ α_val ≤ 1),
                            (@Lottery.mix X _ p r α_val h_α_bounds.1 h_α_bounds.2) ≻ q}

  -- Show S is non-empty using the continuity axiom
  have h_continuity_axiom_applies := PrefRel.continuity p q r h₁ h₂ h₃.2
  let ⟨α_c, _, h_conj_c, h_mix_α_c_pref_q, h_not_q_pref_mix_α_c, _, _⟩ := h_continuity_axiom_applies

  have h_α_c_bounds_strict : 0 < α_c ∧ α_c < 1 := ⟨h_conj_c.1, h_conj_c.2.1⟩
  have h_α_c_bounds : 0 ≤ α_c ∧ α_c ≤ 1 := ⟨le_of_lt h_α_c_bounds_strict.1, le_of_lt h_α_c_bounds_strict.2⟩

  have h_α_c_in_S : α_c ∈ S := by
    use h_α_c_bounds
    unfold strictPref
    constructor
    · exact h_mix_α_c_pref_q
    · exact h_not_q_pref_mix_α_c

  have hS_nonempty : Set.Nonempty S := ⟨α_c, h_α_c_in_S⟩

  -- Show S is bounded below (by 0)
  have hS_bddBelow : BddBelow S := by
    use 0
    intro α_s hα_s
    rcases hα_s with ⟨h_α_bounds_proof, _⟩
    exact h_α_bounds_proof.1

  -- Define α_star as the infimum of S
  let α_star := sInf S

  -- Show that α* exists in [0, 1]
  have h_α_star_nonneg : 0 ≤ α_star := by
    apply le_csInf hS_nonempty
    intro b hb
    rcases hb with ⟨h_b_bounds, _⟩
    exact h_b_bounds.1

  have h_α_star_lt_1_proof : α_star < 1 := by
    have h_sInf_S_le_α_c : α_star ≤ α_c := csInf_le hS_bddBelow h_α_c_in_S
    apply lt_of_le_of_lt h_sInf_S_le_α_c
    exact h_α_c_bounds_strict.2

  have h_α_star_le_one : α_star ≤ 1 := le_of_lt h_α_star_lt_1_proof

  -- Define Lαs outside the inner have block so it's accessible throughout
  let Lαs := @Lottery.mix X _ p r α_star h_α_star_nonneg h_α_star_le_one

  -- First prove that Lαs ≻ q cannot hold
  have not_Lαs_succ_q : ¬ (Lαs ≻ q) := by
    {
    intro h_Lαs_succ_q
    have h_α_star_pos : 0 < α_star := by
      by_contra h_α_star_not_pos
      have h_α_star_eq_0 : α_star = 0 := le_antisymm (le_of_not_lt h_α_star_not_pos) h_α_star_nonneg
      have h_Lαs_eq_r : Lαs = r := by
        apply Subtype.eq
        ext x
        simp [Lottery.mix, Lαs, h_α_star_eq_0]
      rw [h_Lαs_eq_r] at h_Lαs_succ_q
      unfold strictPref at h_Lαs_succ_q
      exact h_Lαs_succ_q.2 h₂
    have h_Lαs_succ_r : Lαs ≻ r := by
      exact (claim_i h₃ α_star h_α_star_pos h_α_star_lt_1_proof).2

    have h_continuity_args_met : PrefRel.pref Lαs q ∧ PrefRel.pref q r ∧ ¬(PrefRel.pref r Lαs) := by
      constructor
      · exact h_Lαs_succ_q.1
      constructor
      · exact h₂
      · exact h_Lαs_succ_r.2

    let ⟨γ_c, _, h_conj_γ_c, h_mix_Lαs_r_γ_c_pref_q, h_not_q_pref_mix_Lαs_r_γ_c, _, _⟩ :=
      PrefRel.continuity Lαs q r h_continuity_args_met.1 h_continuity_args_met.2.1 h_continuity_args_met.2.2

    let α_new := γ_c * α_star

    have h_α_new_lt_α_star : α_new < α_star := by
      have h_γ_c_lt_one : γ_c < 1 := h_conj_γ_c.2.1
      calc α_new = γ_c * α_star := rfl
           _ < 1 * α_star := mul_lt_mul_of_pos_right h_γ_c_lt_one h_α_star_pos
           _ = α_star := one_mul α_star

    have h_α_new_nonneg : 0 ≤ α_new := mul_nonneg (le_of_lt h_conj_γ_c.1) h_α_star_nonneg
    have h_α_new_le_one : α_new ≤ 1 := le_trans (le_of_lt h_α_new_lt_α_star) h_α_star_le_one

    have h_L_α_new_val_eq : (@Lottery.mix X _ Lαs r γ_c (le_of_lt h_conj_γ_c.1) (le_of_lt h_conj_γ_c.2.1)).val =
                           (@Lottery.mix X _ p r α_new h_α_new_nonneg h_α_new_le_one).val := by
      ext x
      simp [Lottery.mix, Lαs]
      ring

    have h_L_α_new_eq : @Lottery.mix X _ Lαs r γ_c (le_of_lt h_conj_γ_c.1) (le_of_lt h_conj_γ_c.2.1) =
                        @Lottery.mix X _ p r α_new h_α_new_nonneg h_α_new_le_one := Subtype.eq h_L_α_new_val_eq

    have h_α_new_in_S : α_new ∈ S := by
      use ⟨h_α_new_nonneg, h_α_new_le_one⟩
      rw [←h_L_α_new_eq]
      exact ⟨h_mix_Lαs_r_γ_c_pref_q, h_not_q_pref_mix_Lαs_r_γ_c⟩
    exact not_lt_of_le (csInf_le hS_bddBelow h_α_new_in_S) h_α_new_lt_α_star
    }
  -- Now we have shown that Lαs ≻ q cannot hold, so we can conclude that Lαs ~ q
  have h_α_star_indiff_q : Lαs ~ q := by
    have not_q_succ_Lαs : ¬(q ≻ Lαs) := by
      intro h_q_succ_Lαs

      have h_p_succ_Lαs : p ≻ Lαs := by
        unfold strictPref
        constructor
        · apply PrefRel.transitive p q Lαs h₁ h_q_succ_Lαs.1
        · intro h_Lαs_pref_p
          have h_Lαs_pref_q := PrefRel.transitive Lαs p q h_Lαs_pref_p h₁
          exact h_q_succ_Lαs.2 h_Lαs_pref_q

      have h_continuity_args_met : PrefRel.pref p q ∧ PrefRel.pref q Lαs ∧ ¬(PrefRel.pref Lαs p) := by
        constructor; exact h₁
        constructor; exact h_q_succ_Lαs.1
        exact h_p_succ_Lαs.2

      let ⟨_, β_c, h_conj_β_c, _, _, h_q_pref_mix_p_Lαs_β_c, h_not_mix_p_Lαs_β_c_pref_q⟩ :=
        PrefRel.continuity p q Lαs h_continuity_args_met.1 h_continuity_args_met.2.1 h_continuity_args_met.2.2

      let α_new := α_star + β_c * (1 - α_star)

      have h_α_star_lt_α_new : α_star < α_new := by
        apply lt_add_of_pos_right
        exact mul_pos h_conj_β_c.2.2.1 (sub_pos_of_lt h_α_star_lt_1_proof)

      have h_α_new_lt_one : α_new < 1 := by
        calc α_new = α_star * (1 - β_c) + β_c := by ring
                 _ < 1 * (1 - β_c) + β_c := by
                   apply add_lt_add_right
                   exact mul_lt_mul_of_pos_right h_α_star_lt_1_proof (sub_pos_of_lt h_conj_β_c.2.2.2)
                 _ = 1 := by
                   rw [one_mul]
                   ring

      have h_α_new_nonneg : 0 ≤ α_new := le_trans h_α_star_nonneg (le_of_lt h_α_star_lt_α_new)
      have h_α_new_le_one : α_new ≤ 1 := le_of_lt h_α_new_lt_one

      have h_L_α_new_val_eq : (@Lottery.mix X _ p Lαs β_c (le_of_lt h_conj_β_c.2.2.1) (le_of_lt h_conj_β_c.2.2.2)).val =
                             (@Lottery.mix X _ p r α_new h_α_new_nonneg h_α_new_le_one).val := by
        ext x
        simp [Lottery.mix, Lαs, α_new]
        ring

      have h_L_α_new_eq : @Lottery.mix X _ p Lαs β_c (le_of_lt h_conj_β_c.2.2.1) (le_of_lt h_conj_β_c.2.2.2) =
                          @Lottery.mix X _ p r α_new h_α_new_nonneg h_α_new_le_one := Subtype.eq h_L_α_new_val_eq

      have h_α_new_not_in_S : α_new ∉ S := by
        intro h_α_new_in_S_contra
        rcases h_α_new_in_S_contra with ⟨_, h_L_α_new_succ_q⟩
        rw [←h_L_α_new_eq] at h_L_α_new_succ_q
        exact h_not_mix_p_Lαs_β_c_pref_q h_L_α_new_succ_q.1

      have h_α_star_not_in_S : α_star ∉ S := by
        intro h_α_star_in_S_contra
        rcases h_α_star_in_S_contra with ⟨_, h_Lαs_succ_q_contra⟩
        exact not_Lαs_succ_q h_Lαs_succ_q_contra

      have exists_s_in_S_between : ∃ s_val ∈ S, α_star < s_val ∧ s_val < α_new := by
        have h_eps : 0 < α_new - α_star := sub_pos_of_lt h_α_star_lt_α_new

        have h_exists_s_between : ∀ y > α_star, ∃ s ∈ S, s < y := by
          intro y hy
          by_contra h_contra
          push_neg at h_contra
          have h_y_lb : ∀ s ∈ S, y ≤ s := by
            intros s hs
            exact h_contra s hs
          have h_y_le_α_star : y ≤ α_star := le_csInf hS_nonempty h_y_lb
          exact not_le_of_gt hy h_y_le_α_star

        let y := (α_star + α_new)/2
        have h_α_star_lt_y : α_star < y := by
          have h_pos_2_real : (0 : Real) < 2 := by norm_num
          have h_mult : 2 * α_star < α_star + α_new := by
            have : 2 * α_star = α_star + α_star := by ring
            rw [this]
            apply add_lt_add_left h_α_star_lt_α_new
          rw [lt_div_iff₀ h_pos_2_real]
          rw [mul_comm] at h_mult
          exact h_mult

        have h_y_lt_α_new : y < α_new := by
          rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
          linarith [h_α_star_lt_α_new]

        rcases h_exists_s_between y h_α_star_lt_y with ⟨s_val, hs_in_S, hs_lt_y⟩

        have hs_lt_α_new : s_val < α_new := lt_trans hs_lt_y h_y_lt_α_new

        have h_α_star_le_s : α_star ≤ s_val := csInf_le hS_bddBelow hs_in_S

        have h_α_star_lt_s : α_star < s_val := by
          apply lt_of_le_of_ne h_α_star_le_s
          intro h_eq
          rw [←h_eq] at hs_in_S
          exact h_α_star_not_in_S hs_in_S

        exact ⟨s_val, hs_in_S, h_α_star_lt_s, hs_lt_α_new⟩

      rcases exists_s_in_S_between with ⟨s_val, hs_in_S, h_α_star_lt_s, hs_lt_α_new⟩
      let Ls := @Lottery.mix X _ p r s_val (le_trans h_α_star_nonneg (le_of_lt h_α_star_lt_s)) (le_trans (le_of_lt hs_lt_α_new) h_α_new_le_one)
      have h_Ls_succ_q : Ls ≻ q := hs_in_S.2
      let Lα_new_lot := @Lottery.mix X _ p r α_new h_α_new_nonneg h_α_new_le_one
      have h_Lα_new_succ_Ls : Lα_new_lot ≻ Ls := claim_ii s_val α_new h₃ (le_trans h_α_star_nonneg (le_of_lt h_α_star_lt_s)) hs_lt_α_new h_α_new_le_one

      have h_Ls_pref_Lα_new : Ls ≿ Lα_new_lot := by
        apply PrefRel.transitive Ls q Lα_new_lot
        · exact h_Ls_succ_q.1
        · unfold Lα_new_lot
          rw [←h_L_α_new_eq]
          exact h_q_pref_mix_p_Lαs_β_c
      exact h_Lα_new_succ_Ls.2 h_Ls_pref_Lα_new

    unfold indiff
    constructor
    · by_cases h : Lαs ≿ q
      · exact h
      · have h_q_pref_Lαs : q ≿ Lαs := Or.resolve_left (PrefRel.complete Lαs q) h
        exact False.elim (not_q_succ_Lαs ⟨h_q_pref_Lαs, h⟩)
    · by_cases h : q ≿ Lαs
      · exact h
      · have h_Lαs_pref_q : Lαs ≿ q := Or.resolve_right (PrefRel.complete Lαs q) h
        exact False.elim (not_Lαs_succ_q ⟨h_Lαs_pref_q, h⟩)

  -- Define uniqueness lemma before using it
  have uniqueness : ∀ (α β : Real) (hα_nonneg : 0 ≤ α) (hα_le_1 : α ≤ 1) (hβ_nonneg : 0 ≤ β) (hβ_le_1 : β ≤ 1),
                       indiff (@Lottery.mix X _ p r α hα_nonneg hα_le_1) q →
                       indiff (@Lottery.mix X _ p r β hβ_nonneg hβ_le_1) q → α = β := by
    intro α β hα_nonneg hα_le_1 hβ_nonneg hβ_le_1 h_mix_α h_mix_β
    by_contra h_neq
    -- If α ≠ β, then either α < β or β < α
    cases lt_or_gt_of_ne h_neq with
    | inl h_α_lt_β => -- Case α < β
      -- By claim_ii, if 0 ≤ α < β ≤ 1, then mix p r β ≻ mix p r α
      -- This follows from the monotonicity of mixing probabilities.
      have h_mix_strict := claim_ii α β h₃ hα_nonneg h_α_lt_β hβ_le_1

      -- We also know mix p r α ~ q and mix p r β ~ q
      -- By transitivity of the preference relation, mix p r α ≿ mix p r β
      unfold indiff at h_mix_α h_mix_β
      have h_α_pref_β : PrefRel.pref (@Lottery.mix X _ p r α hα_nonneg (le_trans (le_of_lt h_α_lt_β) hβ_le_1))
                                   (@Lottery.mix X _ p r β (le_trans hα_nonneg (le_of_lt h_α_lt_β)) hβ_le_1) := by
        -- Use transitivity: mix p r α ≿ q and q ≿ mix p r β imply mix p r α ≿ mix p r β
        apply PrefRel.transitive _ q _
        · exact h_mix_α.1  -- mix p r α ≿ q
        · exact h_mix_β.2  -- q ≿ mix p r β

      -- But this contradicts h_mix_strict.2, which states ¬(mix p r α ≿ mix p r β)
      unfold strictPref at h_mix_strict
      exact h_mix_strict.2 h_α_pref_β
    | inr h_β_lt_α => -- Case β < α
      -- Similarly, if β < α, then mix p r α ≻ mix p r β
      -- This follows from the monotonicity of mixing probabilities.
      have h_mix_strict := claim_ii β α h₃ hβ_nonneg h_β_lt_α hα_le_1

      -- We also know mix p r α ~ q and mix p r β ~ q
      -- By transitivity of the preference relation, mix p r β ≿ mix p r α
      unfold indiff at h_mix_α h_mix_β
      have h_β_pref_α : PrefRel.pref (@Lottery.mix X _ p r β hβ_nonneg (le_trans (le_of_lt h_β_lt_α) hα_le_1))
                                   (@Lottery.mix X _ p r α (le_trans hβ_nonneg (le_of_lt h_β_lt_α)) hα_le_1) := by
        -- Use transitivity: mix p r β ≿ q and q ≿ mix p r α imply mix p r β ≿ mix p r α
        apply PrefRel.transitive _ q _
        · exact h_mix_β.1  -- mix p r β ≿ q
        · exact h_mix_α.2  -- q ≿ mix p r α

      -- But this contradicts h_mix_strict.2, which states ¬(mix p r β ≿ mix p r α)
      unfold strictPref at h_mix_strict
      exact h_mix_strict.2 h_β_pref_α

  -- Construct the subtype element from α_star
  use ⟨α_star, h_α_star_nonneg, h_α_star_le_one⟩

  constructor
  · -- Show that this α_star satisfies the property
    exact h_α_star_indiff_q
  · -- Show uniqueness
    intro β hβ_indiff
    -- β is of type ↥(Set.Icc (0:Real) 1), so β.val is the real number
    -- and β.property gives us the bounds
    apply Subtype.eq
    exact uniqueness β.val α_star β.property.1 β.property.2 h_α_star_nonneg h_α_star_le_one hβ_indiff h_α_star_indiff_q

-- Transitivity helper for p ~ l, l ≿ q => p ≿ q
lemma PrefRel.transitive_pref_indiff_left {p l q : Lottery X} (h_l_pref_q : l ≿ q) (h_p_sim_l : p ~ l) : p ≿ q :=
  PrefRel.transitive p l q h_p_sim_l.1 h_l_pref_q

-- Transitivity helper for p ≿ l, l ~ q => p ≿ q
lemma PrefRel.transitive_pref_indiff_right {p l q : Lottery X} (h_p_pref_l : p ≿ l) (h_l_sim_q : l ~ q) : p ≿ q :=
  PrefRel.transitive p l q h_p_pref_l h_l_sim_q.1

/--Theorem 6.1  Expected utility representation theorem (exists).-/
theorem vNM_theorem [DecidableEq X] :
  ∃ u : X → Real, ∀ p q : Lottery X, (p ≿ q) ↔ (expectedUtility p u ≥ expectedUtility q u) := by
  -- Use the continuity axiom to show that the expected utility function is continuous
  -- and satisfies the properties of the vNM theorem
  -- The continuity axiom states that if p ≿ q ≿ r, then there exists a γ ∈ (0, 1)
  let δ : X → Lottery X := fun x_val =>
    ⟨fun y => if y = x_val then 1 else 0, by
      constructor
      · intro y; by_cases h : y = x_val <;> simp [h]
      · simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]⟩

  -- Define local Preorder instance using PrefRel.pref
  letI preorder_Lottery_pref : Preorder (Lottery X) := {
    le := PrefRel.pref,
    lt := strictPref,
    le_refl := PrefRel.refl,
    le_trans := PrefRel.transitive,
    lt_iff_le_not_le := fun _ _ => Iff.rfl
  }
  -- The global IsTotal instance for PrefRel.pref will be used by Finset.exists_forall_le/ge

  -- Prove existence of x_star, x_circ such that p_star = δ x_star and p_circ = δ x_circ
  -- are maximal and minimal among degenerate lotteries.
  let s_univ := Finset.image δ Finset.univ
  have hs_nonempty : s_univ.Nonempty := (Finset.univ_nonempty (α := X)).image δ

  have exists_x_star_node : ∃ x_s : X, ∀ x : X, (δ x_s) ≿ (δ x) := by
    -- Finset.exists_maximal provides an element m such that m ∈ s_univ and ∀ a ∈ s_univ, a ≿ m → m ≿ a.
    -- Since PrefRel.pref is a total order, this gives us a "greatest" element w.r.t. ≿.
    -- To get a greatest element (m such that m ≿ a for all a), we use Finset.exists_minimal.
    let h_greatest_lottery := Finset.exists_minimal s_univ hs_nonempty
    rcases h_greatest_lottery with ⟨p_s, ⟨hp_s_in_s_univ, h_ps_le_all⟩⟩
    obtain ⟨x_s, _, h_ps_eq_delta_xs⟩ := Finset.mem_image.mp hp_s_in_s_univ
    use x_s
    intro x'
    rw [h_ps_eq_delta_xs]

    -- Show δ x' ∈ s_univ
    have h_delta_x'_in_s_univ : δ x' ∈ s_univ := Finset.mem_image_of_mem δ (Finset.mem_univ x')

    -- Use h_ps_le_all to show ¬(δ x' < p_s)
    have h_not_delta_x'_lt_p_s : ¬(strictPref (δ x') p_s) := h_ps_le_all (δ x') h_delta_x'_in_s_univ

    -- Expand the definition of strictPref and apply De Morgan's laws
    unfold strictPref at h_not_delta_x'_lt_p_s
    push_neg at h_not_delta_x'_lt_p_s

    -- Now h_not_delta_x'_lt_p_s is: (δ x' ≿ p_s) → p_s ≿ δ x'
    by_cases h : δ x' ≿ p_s
    · -- If δ x' ≿ p_s, then p_s ≿ δ x' by h_not_delta_x'_lt_p_s
      exact h_not_delta_x'_lt_p_s h
    · -- If ¬(δ x' ≿ p_s), then by completeness, p_s ≿ δ x'
      cases PrefRel.complete (δ x') p_s with
      | inl h_contradiction => exact False.elim (h h_contradiction)
      | inr h_p_s_pref_delta_x' => exact h_p_s_pref_delta_x'

  have exists_x_circ_node : ∃ x_c : X, ∀ x : X, (δ x) ≿ (δ x_c) := by
    -- Use the fact that there exists a maximal element in the finite set s_univ
    have h_exists_max := Finset.exists_maximal s_univ hs_nonempty
    obtain ⟨p_max, hp_max_in_s, hp_max_maximal⟩ := h_exists_max

    -- Extract the corresponding x_c from p_max = δ x_c
    obtain ⟨x_c, _, hp_max_eq⟩ := Finset.mem_image.mp hp_max_in_s
    use x_c

    intro x
    -- We need to show δ x ≿ δ x_c
    -- We know p_max = δ x_c and p_max is maximal in s_univ
    -- Since δ x ∈ s_univ, we have that δ x ≿ p_max implies p_max ≿ δ x
    have h_delta_x_in_s : δ x ∈ s_univ := Finset.mem_image_of_mem δ (Finset.mem_univ x)

    -- Use the maximality property of p_max
    have h_max_prop := hp_max_maximal (δ x) h_delta_x_in_s
    -- h_max_prop : strictPref (δ x) p_max → strictPref p_max (δ x)

    -- We need to consider both cases by completeness
    cases PrefRel.complete (δ x) p_max with
    | inl h_delta_pref_pmax =>
      -- If δ x ≿ p_max, check if it's strict preference
      by_cases h_strict : strictPref (δ x) p_max
      · -- If δ x ≻ p_max, then by maximality, p_max ≻ δ x, which gives p_max ≿ δ x
        rw [hp_max_eq]
        -- If δ x ≻ p_max, then δ x ≿ p_max by definition of ≻.
        exact h_strict.1
      · -- If ¬(δ x ≻ p_max), then either δ x ~ p_max or p_max ≿ δ x
        -- Since we have δ x ≿ p_max and ¬(δ x ≻ p_max), we must have δ x ~ p_max
        have h_indiff : indiff (δ x) p_max := by
          unfold indiff
          unfold strictPref at h_strict
          push_neg at h_strict
          exact ⟨h_delta_pref_pmax, h_strict h_delta_pref_pmax⟩
        rw [hp_max_eq]
        exact h_indiff.1
    | inr h_pmax_pref_delta => -- p_max ≿ δ x
      rw [hp_max_eq] -- Goal is now δ x ≿ δ x_c (which is p_max)
      -- We have h_pmax_pref_delta : p_max ≿ δ x.
      -- From maximality of p_max: hp_max_maximal (δ x) h_delta_x_in_s is ¬ (strictPref p_max (δ x)).
      -- If ¬(δ x ≿ p_max), then (p_max ≿ δ x ∧ ¬(δ x ≿ p_max)) would mean (strictPref p_max (δ x)).
      -- This would contradict hp_max_maximal.
      -- Therefore, δ x ≿ p_max must be true.
      by_contra h_not_delta_x_pref_pmax
      exact (hp_max_maximal (δ x) h_delta_x_in_s) ⟨h_pmax_pref_delta, h_not_delta_x_pref_pmax⟩
  -- Now we have x_star and x_circ such that δ x_star is maximal and δ x_circ is minimal
  -- among degenerate lotteries. We can use these to define the utility function u.
  -- We need to show that δ x_star and δ x_circ are not indifferent


  let x_star := Classical.choose exists_x_star_node
  let p_star := δ x_star
  have h_p_star_is_max : ∀ x : X, p_star ≿ δ x := Classical.choose_spec exists_x_star_node

  let x_circ := Classical.choose exists_x_circ_node
  let p_circ := δ x_circ
  have h_p_circ_is_min : ∀ x : X, δ x ≿ p_circ := Classical.choose_spec exists_x_circ_node

  -- Helper: Indifference relation is symmetric
  let indiff_symmetric (l1 l2 : Lottery X) (h : l1 ~ l2) : l2 ~ l1 := ⟨h.2, h.1⟩

  -- Define the utility function u
  let u : X → Real := by
    classical
    exact if h : p_star ~ p_circ then
      fun _ => 0 -- Case 1: All outcomes are indifferent
    else
      fun x => -- Case 2: p_star ≻ p_circ
        let h_ps_succ_pc : p_star ≻ p_circ := by
          unfold strictPref
          constructor
          · exact h_p_star_is_max x_circ
          · unfold indiff at h
            push_neg at h
            -- We have h : (p_star ≿ p_circ) → ¬p_circ ≿ p_star
            -- We know p_star ≿ p_circ from h_p_star_is_max x_circ
            -- So we can apply h to get ¬p_circ ≿ p_star
            exact h (h_p_star_is_max x_circ)
        (Classical.choose (claim_v (h_p_star_is_max x) (h_p_circ_is_min x) h_ps_succ_pc)).val
  use u

  -- Helper for L(α) := α p_star + (1-α) p_circ
  let L_mix (α : Real) (h_α_nonneg : 0 ≤ α) (h_α_le_one : α ≤ 1) : Lottery X :=
    @Lottery.mix X _ p_star p_circ α h_α_nonneg h_α_le_one

  -- Property: 0 ≤ u(x) ≤ 1
  have h_u_bounds : ∀ x, 0 ≤ u x ∧ u x ≤ 1 := by
    intro x
    simp only [u]
    split_ifs with h_ps_sim_pc
    · simp [h_ps_sim_pc] -- u(x) = 0, so 0 ≤ 0 ∧ 0 ≤ 1
    · -- u(x) is from Claim V, which guarantees α ∈ [0,1] (specifically, Subtype from Set.Icc)
      let h_ps_succ_pc : p_star ≻ p_circ := by
        unfold strictPref
        constructor
        · exact h_p_star_is_max x_circ
        · unfold indiff at h_ps_sim_pc
          push_neg at h_ps_sim_pc
          -- We have h_ps_sim_pc : (p_star ≿ p_circ) → ¬p_circ ≿ p_star
          -- We know p_star ≿ p_circ from h_p_star_is_max x_circ
          -- So we can apply h_ps_sim_pc to get ¬p_circ ≿ p_star
          exact h_ps_sim_pc (h_p_star_is_max x_circ)
      exact (Classical.choose (claim_v (h_p_star_is_max x) (h_p_circ_is_min x) h_ps_succ_pc)).property

  -- Property: δ x ~ L(u x)
  have h_delta_sim_L_ux : ∀ x, δ x ~ L_mix (u x) (h_u_bounds x).1 (h_u_bounds x).2 := by
    intro x
    unfold u
    split_ifs with h_ps_sim_pc
    · -- p_star ~ p_circ. u(x) = 0. Need δ x ~ L(0) = p_circ.
      -- First show L_mix 0 _ _ = p_circ
      have h_L0_eq_pcirc : L_mix 0 (by linarith) (by linarith) = p_circ := by
        apply Subtype.eq; ext y; simp [L_mix, Lottery.mix]

      -- Now use this equality to prove δ x ~ p_circ
      rw [h_L0_eq_pcirc]
      -- Since δ x ≿ p_circ and p_circ ≿ δ x, we have δ x ~ p_circ.
      exact ⟨h_p_circ_is_min x,
             PrefRel.transitive p_circ p_star (δ x) h_ps_sim_pc.2 (h_p_star_is_max x)⟩
    · -- p_star ≻ p_circ. u(x) is α_x from Claim V.
      -- Claim V gives L(u x) ~ δ x. indiff is symmetric.
      let h_ps_succ_pc : p_star ≻ p_circ := by
        unfold strictPref
        constructor
        · exact h_p_star_is_max x_circ
        · -- We need to prove ¬(p_circ ≿ p_star) from h_ps_sim_pc : ¬(p_star ~ p_circ)
          intro h_circ_pref_star
          apply h_ps_sim_pc
          unfold indiff
          exact ⟨h_p_star_is_max x_circ, h_circ_pref_star⟩
      -- Extract just the indifference relation from the conjunction returned by Classical.choose_spec
      let h_mix_sim_delta := (Classical.choose_spec (claim_v (h_p_star_is_max x) (h_p_circ_is_min x) h_ps_succ_pc)).1
      -- Directly construct the symmetric indifference relation
      exact ⟨h_mix_sim_delta.2, h_mix_sim_delta.1⟩

  -- Property: 0 ≤ expectedUtility p u ≤ 1
  have h_EU_bounds : ∀ p : Lottery X, 0 ≤ expectedUtility p u ∧ expectedUtility p u ≤ 1 := by
    intro p
    -- Use the bounds of u to show the bounds of expectedUtility
    have h_supp_nonempty : (Finset.filter (fun x => p.val x ≠ 0) Finset.univ).Nonempty := by
        by_contra h_not_nonempty
        rw [Finset.not_nonempty_iff_eq_empty] at h_not_nonempty
        have h_all_px_zero : ∀ x, p.val x = 0 := by
          intro x
          by_contra h_px_ne_zero
          have x_mem_filter : x ∈ Finset.filter (fun y => p.val y ≠ 0) Finset.univ :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ x, h_px_ne_zero⟩
          rw [h_not_nonempty] at x_mem_filter
          exact Finset.not_mem_empty x x_mem_filter
        have h_sum_is_zero : ∑ x, p.val x = 0 :=
          Finset.sum_eq_zero_iff_of_nonneg (fun i _ => p.property.1 i) |>.mpr (fun i _ => h_all_px_zero i)
        rw [p.property.2] at h_sum_is_zero -- h_sum_is_zero is now 1 = 0
        exact zero_ne_one h_sum_is_zero.symm -- h_sum_is_zero.symm is 0 = 1, zero_ne_one is 0 ≠ 1
    have h_supp_card_pos : 0 < Finset.card (Finset.filter (fun x => p.val x ≠ 0) Finset.univ) := by
      exact Finset.card_pos.mpr h_supp_nonempty

    -- Use the bounds of u to show the bounds of expectedUtility
    have h_EU_nonneg : 0 ≤ expectedUtility p u := by
      apply Finset.sum_nonneg
      intro x hx
      have h_p_nonneg : 0 ≤ p.val x := p.property.1 x
      have h_u_nonneg : 0 ≤ u x := (h_u_bounds x).1
      exact mul_nonneg h_p_nonneg h_u_nonneg

    have h_EU_le_one : expectedUtility p u ≤ 1 := by
      -- Define what expectedUtility is
      have h_EU_def : expectedUtility p u = ∑ x ∈ Finset.filter (fun x => p.val x ≠ 0) Finset.univ, p.val x * u x := rfl

      -- Since u x ≤ 1 for all x, and p.val x ≥ 0, we have p.val x * u x ≤ p.val x
      have h_term_le : ∀ x ∈ Finset.filter (fun x => p.val x ≠ 0) Finset.univ, p.val x * u x ≤ p.val x := by
        intro x hx
        apply mul_le_of_le_one_right
        · exact p.property.1 x  -- p.val x ≥ 0
        · exact (h_u_bounds x).2  -- u x ≤ 1

      -- Sum of terms is less than or equal to sum of upper bounds
      have h_sum_le : (∑ x ∈ Finset.filter (fun x => p.val x ≠ 0) Finset.univ, p.val x * u x) ≤
                     (∑ x ∈ Finset.filter (fun x => p.val x ≠ 0) Finset.univ, p.val x) := by
        apply Finset.sum_le_sum
        exact h_term_le

      -- The sum of p.val x over the support equals the sum over all x
      have h_sum_eq : (∑ x ∈ Finset.filter (fun x => p.val x ≠ 0) Finset.univ, p.val x) =
                     (∑ x, p.val x) := by
        -- Since p.val x = 0 for x not in the support
        symm
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro x _
        by_cases h : p.val x ≠ 0
        · simp [h]
        · push_neg at h  -- Convert ¬(p.val x ≠ 0) to p.val x = 0
          simp [h]
        -- This shows that the sum over the support is equal to the sum over all x

      -- And the sum of all p.val x is 1
      have h_sum_one : (∑ x, p.val x) = 1 := p.property.2

      -- Chain the inequalities together using trans instead of calc
      trans (∑ x ∈ Finset.filter (fun x => p.val x ≠ 0) Finset.univ, p.val x)
      · rw [h_EU_def]
        exact h_sum_le
      rw [h_sum_eq, h_sum_one]

    exact ⟨h_EU_nonneg, h_EU_le_one⟩

  -- Move h_p_sim_L_EU_p definition here, before its first usage
  -- Key Lemma: p ~ L(expectedUtility p u)
  have h_p_sim_L_EU_p : ∀ (p : Lottery X),
      p ~ L_mix (expectedUtility p u) (h_EU_bounds p).1 (h_EU_bounds p).2 := by {
    intro p
    -- Proof by induction on the size of the support of p_lottery
    let motive (k : ℕ) (p : Lottery X) : Prop :=
      Finset.card (Finset.filter (fun x => p.val x ≠ 0) Finset.univ) = k → p ~ L_mix (expectedUtility p u) (h_EU_bounds p).1 (h_EU_bounds p).2
    suffices h : ∀ k ≤ Fintype.card X, ∀ p, motive k p by
      exact h (Finset.card (Finset.filter (fun x => p.val x ≠ 0) Finset.univ)) (Finset.card_le_univ _) p rfl

    apply @Nat.strong_induction_on (λ k_max => ∀ k ≤ k_max, ∀ p, motive k p) (Fintype.card X)
    clear p
    intros k_max h_ind_hyp k hk_le_k_max p hk_eq_k
    let supp_card := Finset.card (Finset.filter (fun x => p.val x ≠ 0) Finset.univ)
    by_cases h_supp_card_eq_1 : supp_card = 1
    · -- Base case: support size is 1, so p_lottery = δ x for some x
      -- Extract the unique element from the support
      let supp := Finset.filter (fun x => p.val x ≠ 0) Finset.univ
      have h_supp_card : supp.card = 1 := h_supp_card_eq_1
      have h_supp_nonempty : supp.Nonempty := by
        rw [←Finset.card_pos, h_supp_card]; norm_num
      let x₀ := Classical.choose h_supp_nonempty
      have hx₀_in_supp : x₀ ∈ supp := Classical.choose_spec h_supp_nonempty
      have h_supp_eq_singleton : supp = {x₀} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        constructor
        · exact hx₀_in_supp
        · intro y hy -- hy : y ∈ supp. Goal: y = x₀
          -- h_supp_card_eq_1 : supp.card = 1 is in scope (from the by_cases h_supp_card_eq_1)
          have h_subset_for_card_le : {x₀, y} ⊆ supp := by
            intro z hz_mem_pair
            simp at hz_mem_pair
            cases hz_mem_pair with
            | inl hz_eq_x₀ => rw [hz_eq_x₀]; exact hx₀_in_supp
            | inr hz_eq_y  => rw [hz_eq_y]; exact hy

          apply Classical.byContradiction
          intro h_y_ne_x₀ -- h_y_ne_x₀ : y ≠ x₀ (because the goal is y = x₀)

          have h_card_pair_is_2 : Finset.card ({x₀, y} : Finset X) = 2 := Finset.card_pair (Ne.symm h_y_ne_x₀)

          have h_2_le_supp_card : 2 ≤ supp.card := by
            rw [←h_card_pair_is_2] -- Substitute card {x₀,y} with 2
            exact Finset.card_le_card h_subset_for_card_le

          -- We have h_2_le_supp_card : 2 ≤ supp.card
          -- And h_supp_card_eq_1 : supp.card = 1
          -- linarith should find the contradiction.
          linarith [h_2_le_supp_card, h_supp_card_eq_1]

      have p_eq_delta_x₀ : p.val = (δ x₀).val := by
        ext y
        by_cases hy_eq_x₀ : y = x₀
        · -- Case y = x₀
          rw [hy_eq_x₀]
          simp [δ]
          -- Need to show p.val x₀ = 1
          have : ∑ x ∈ supp, p.val x = 1 := by
            -- supp is defined as Finset.filter (fun x => p.val x ≠ 0) Finset.univ
            -- We need to show that summing over supp equals summing over univ
            have : ∑ x ∈ supp, p.val x = ∑ x ∈ Finset.univ, p.val x := by
              apply Finset.sum_subset (Finset.filter_subset _ _)
              intro x _ hx_not_in_supp
              -- If x is not in supp, then p.val x = 0
              simp [supp, Finset.mem_filter] at hx_not_in_supp
              exact hx_not_in_supp
            rw [this]
            exact p.2.2
          rw [h_supp_eq_singleton] at this
          rw [Finset.sum_singleton] at this
          exact this
        · -- Case y ≠ x₀
          simp [δ, hy_eq_x₀]
          -- Need to show p.val y = 0
          -- Original proof used `by_contra h_p_val_y_ne_zero`.
          -- Replaced with `by_cases` to resolve potential identifier issue.
          by_cases h_pval_y_eq_zero_alt : p.val y = 0
          · -- If p.val y = 0, this branch is proven.
            assumption
          · -- Otherwise, p.val y ≠ 0. We derive a contradiction.
            -- h_pval_y_eq_zero_alt : p.val y ≠ 0 is in context.
            have hy_in_supp : y ∈ supp := Finset.mem_filter.mpr ⟨Finset.mem_univ y, h_pval_y_eq_zero_alt⟩
            rw [h_supp_eq_singleton] at hy_in_supp -- hy_in_supp is now y ∈ {x₀}
            simp at hy_in_supp -- hy_in_supp is now y = x₀
            -- We have hy_eq_x₀ : y ≠ x₀ (from the outer by_cases on y = x₀)
            -- and hy_in_supp : y = x₀. This is a contradiction.
            -- The goal of this branch is p.val y = 0.
            -- We have h_pval_y_eq_zero_alt : p.val y ≠ 0.
            -- So, from the contradiction (y ≠ x₀ ∧ y = x₀), we can prove False,
            -- and from False, we can prove the goal p.val y = 0 (via h_pval_y_eq_zero_alt).
            exact False.elim (hy_eq_x₀ hy_in_supp)
      rw [show p = δ x₀ by exact Subtype.eq p_eq_delta_x₀]
      simp [expectedUtility, δ, Finset.sum_ite_eq', Finset.mem_univ, if_pos rfl, mul_one, mul_zero, Finset.sum_const_zero, add_zero]
      exact h_delta_sim_L_ux x₀
    · -- Inductive step: supp_card > 1
      have val_ne_zero_of_sum_eq_one_p : p.val ≠ (fun _ => 0) := by
        intro h_absurd_pval_is_zero
        have sum_is_one : ∑ x, p.val x = 1 := p.property.2
        rw [h_absurd_pval_is_zero] at sum_is_one
        simp only [Finset.sum_const_zero] at sum_is_one
        exact zero_ne_one sum_is_one

      have h_supp_card_gt_1 : 1 < supp_card := by
        -- Since p is not the zero function, its support is non-empty
        have h_supp_nonempty : (Finset.filter (fun x => p.val x ≠ 0) Finset.univ).Nonempty := by {
          -- Use the definition of Finset.Nonempty directly
          use Classical.choose (not_forall.mp (fun h_all_zero => val_ne_zero_of_sum_eq_one_p (funext h_all_zero)))
          simp [Finset.mem_filter]
          exact Classical.choose_spec (not_forall.mp (fun h_all_zero => val_ne_zero_of_sum_eq_one_p (funext h_all_zero)))
        }
        -- Since the support is non-empty, its cardinality is at least 1
        have : 1 ≤ supp_card := Finset.card_pos.mpr h_supp_nonempty
        -- Combined with h_supp_card_eq_1, we get 1 < supp_card
        exact lt_of_le_of_ne this (Ne.symm h_supp_card_eq_1)

      have supp_nonempty : (Finset.filter (fun x => p.val x ≠ 0) Finset.univ).Nonempty := by {
        rw [Finset.nonempty_iff_ne_empty]
        intro h_empty
        have h_all_px_zero : ∀ x, p.val x = 0 := by
          intro x
          have : x ∉ Finset.filter (fun x => p.val x ≠ 0) Finset.univ := by
            rw [h_empty]
            simp
          simp [Finset.mem_filter] at this
          exact this
        have h_pval_is_zero_fn : p.val = (fun _ => 0) := funext h_all_px_zero
        exact val_ne_zero_of_sum_eq_one_p h_pval_is_zero_fn
      }
      let x₀ := supp_nonempty.choose
      let α₀ := p.val x₀
      have h_α₀_pos : 0 < α₀ := by
        -- α₀ = p.val x₀, and x₀ is in the support of p
        have : x₀ ∈ Finset.filter (fun x => p.val x ≠ 0) Finset.univ := supp_nonempty.choose_spec
        simp [Finset.mem_filter] at this
        exact lt_of_le_of_ne (p.property.1 x₀) (Ne.symm this)
      have h_α₀_le_1 : α₀ ≤ 1 := by
        have h_singleton_subset : {x₀} ⊆ Finset.univ := by simp
        have h_sum := p.property.2
        rw [←h_sum]
        apply Finset.single_le_sum
        · intros x _
          exact p.property.1 x
        · simp
      have h_α₀_lt_1 : α₀ < 1 := by
        by_contra h_not_lt
        have h_eq : α₀ = 1 := le_antisymm h_α₀_le_1 (le_of_not_lt h_not_lt)
        have : ∑ x ∈ Finset.univ \ { x₀ }, p.val x = ∑ x ∈ Finset.univ, p.val x - p.val x₀ := by
          rw [← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr (Finset.mem_univ x₀))]
          simp [Finset.sum_singleton]
        -- If α₀ = 1, then p.val x₀ = 1, which means p = δ x₀
        have h_sum : ∑ x, p.val x = 1 := p.property.2
        -- Since α₀ = p.val x₀ and α₀ = 1, we have p.val x₀ = 1
        have h_p_x₀_eq_1 : p.val x₀ = 1 := h_eq
        -- This means all other values must be 0
        have : ∀ y ≠ x₀, p.val y = 0 := by
          intro y hy
          by_contra h_pos
          have h_pos' : 0 < p.val y := lt_of_le_of_ne (p.property.1 y) (Ne.symm h_pos)
          have : 1 < ∑ x, p.val x := by
            calc 1 = α₀ := h_eq.symm
                 _ = p.val x₀ := rfl
                 _ < p.val x₀ + p.val y := by linarith
                 _ ≤ ∑ x, p.val x := by
                   have h_x₀_mem : x₀ ∈ Finset.univ := Finset.mem_univ x₀
                   have h_y_mem : y ∈ Finset.univ := Finset.mem_univ y
                   have h_subset : {x₀, y} ⊆ Finset.univ := by simp
                   have h_sum_pair : ∑ x ∈ { x₀, y }, p.val x = p.val x₀ + p.val y := by
                     rw [Finset.sum_pair (Ne.symm hy)]
                   rw [←h_sum_pair]
                   apply Finset.sum_le_sum_of_subset_of_nonneg h_subset
                   intros x _ _
                   exact p.property.1 x
          linarith [p.property.2]
        -- This means the support has cardinality 1
        have : Finset.filter (fun x => p.val x ≠ 0) Finset.univ = {x₀} := by
          ext y
          simp [Finset.mem_filter]
          constructor
          · intro hy
            by_contra h_ne
            have : p.val y = 0 := this y h_ne
            contradiction
          · intro hy
            rw [hy]
            linarith
        have : supp_card = 1 := by
          unfold supp_card
          rw [this]
          simp
        exact h_supp_card_eq_1 this

      have supp_nonempty_alt : (Finset.filter (fun x => p.val x ≠ 0) Finset.univ).Nonempty := by
        by_contra h_empty
        simp [Finset.not_nonempty_iff_eq_empty] at h_empty
        have : ∀ x, p.val x = 0 := by
          intro x
          have : x ∉ Finset.filter (fun x => p.val x ≠ 0) Finset.univ := by
            rw [h_empty]
            simp
          simp [Finset.mem_filter] at this
          exact this
        have : p.val = fun _ => 0 := funext this
        exact val_ne_zero_of_sum_eq_one_p this
      let x₀ := supp_nonempty_alt.choose
      let α₀ := p.val x₀
      have h_α₀_pos : 0 < α₀ := by
        -- x₀ is in the support of p, meaning p.val x₀ ≠ 0
        have hx₀_in_supp : x₀ ∈ Finset.filter (fun x => p.val x ≠ 0) Finset.univ :=
          supp_nonempty_alt.choose_spec
        simp [Finset.mem_filter] at hx₀_in_supp
        exact lt_of_le_of_ne (p.property.1 x₀) (Ne.symm hx₀_in_supp)
      have h_α₀_le_1 : α₀ ≤ 1 := by exact (Finset.single_le_sum (fun i _ => p.property.1 i) (Finset.mem_univ x₀)).trans p.property.2.le
      have h_α₀_lt_1 : α₀ < 1 := by
        by_contra h_not_lt
        have h_eq : α₀ = 1 := le_antisymm h_α₀_le_1 (le_of_not_lt h_not_lt)
        -- If α₀ = 1, then p.val x₀ = 1, which means p = δ x₀
        have h_sum : ∑ x, p.val x = 1 := p.property.2
        -- Since α₀ = p.val x₀ and α₀ = 1, we have p.val x₀ = 1
        have h_p_x₀_eq_1 : p.val x₀ = 1 := h_eq
        -- This means all other values must be 0
        have : ∀ y ≠ x₀, p.val y = 0 := by
          intro y hy
          by_contra h_pos
          have h_pos' : 0 < p.val y := lt_of_le_of_ne (p.property.1 y) (Ne.symm h_pos)
          have : 1 < ∑ x, p.val x := by
            calc 1 = α₀ := h_eq.symm
                 _ = p.val x₀ := rfl
                 _ < p.val x₀ + p.val y := by linarith
                 _ ≤ ∑ x, p.val x := by
                   have h_x₀_mem : x₀ ∈ Finset.univ := Finset.mem_univ x₀
                   have h_y_mem : y ∈ Finset.univ := Finset.mem_univ y
                   have h_subset : {x₀, y} ⊆ Finset.univ := by simp
                   have h_sum_pair : ∑ x ∈ { x₀, y }, p.val x = p.val x₀ + p.val y := by
                     rw [Finset.sum_pair (Ne.symm hy)]
                   rw [←h_sum_pair]
                   apply Finset.sum_le_sum_of_subset_of_nonneg h_subset
                   intros x _ _
                   exact p.property.1 x
          linarith [p.property.2]
        -- This means the support has cardinality 1
        have : Finset.filter (fun x => p.val x ≠ 0) Finset.univ = {x₀} := by
          ext y
          simp [Finset.mem_filter]
          constructor
          · intro hy
            by_contra h_ne
            have : p.val y = 0 := this y h_ne
            exact hy this
          · intro hy
            rw [hy]
            linarith
        have : supp_card = 1 := by
          unfold supp_card
          rw [this]
          simp
        exact h_supp_card_eq_1 this

      -- Define p' such that p = α₀ δ x₀ + (1-α₀) p'
      let p' : Lottery X := ⟨fun x => if x = x₀ then 0 else p.val x / (1 - α₀), by
        constructor
        · intro x
          by_cases hx_eq_x₀ : x = x₀
          · simp [hx_eq_x₀]
          · simp [hx_eq_x₀]
            exact div_nonneg (p.2.1 x) (by linarith [h_α₀_lt_1])
        · calc ∑ x, (if x = x₀ then 0 else p.val x / (1 - α₀))
              = ∑ x ∈ Finset.univ.filter (· ≠ x₀), p.val x / (1 - α₀) := by
                rw [Finset.sum_filter]
                congr 1
                ext x
                by_cases h_eq : x = x₀ <;> simp [h_eq]
              _ = (∑ x ∈ Finset.univ.filter (· ≠ x₀), p.val x) / (1 - α₀) := by
                simp_rw [div_eq_mul_inv]; rw [Finset.sum_mul]
              _ = (1 - α₀) / (1 - α₀) := by
                congr 1
                -- We need to show ∑_{x ≠ x₀} p.val x = 1 - α₀
                have h_sum_split : ∑ x ∈ Finset.univ, p.val x = p.val x₀ + ∑
                  x ∈ Finset.univ.filter (· ≠ x₀), p.val x := by
                  rw [← Finset.sum_filter_add_sum_filter_not _ (· = x₀)]
                  simp only [Finset.filter_eq', Finset.mem_univ, if_true, Finset.sum_singleton]
                rw [p.property.2] at h_sum_split
                linarith [h_sum_split]
              _ = 1 := by
                exact div_self (by linarith [h_α₀_lt_1])
          ⟩

      have h_p_eq_mix_val : p.val = (@Lottery.mix X _ (δ x₀) p' α₀ (le_of_lt h_α₀_pos) h_α₀_le_1).val := by
        ext x
        by_cases hx_eq_x₀ : x = x₀
        · -- Case: x = x₀
          unfold Lottery.mix δ p'
          simp only [hx_eq_x₀, if_true]
          ring
        · -- Case: x ≠ x₀
          unfold Lottery.mix δ p'
          simp only [hx_eq_x₀, if_false, if_neg (Ne.symm hx_eq_x₀)]
          -- Goal: p.val x = α₀ * 0 + (1 - α₀) * (p.val x / (1 - α₀))
          have h_denom_ne_zero : 1 - α₀ ≠ 0 := by linarith [h_α₀_lt_1]
          field_simp [h_denom_ne_zero]
          -- Goal after field_simp: p.val x = p.val x, which is closed by rfl (implicitly)
      rw [show p = @Lottery.mix X _ (δ x₀) p' α₀ (le_of_lt h_α₀_pos) h_α₀_le_1 by exact Subtype.eq h_p_eq_mix_val]

      have h_supp_p'_lt : Finset.card (Finset.filter (fun x => p'.val x ≠ 0) Finset.univ) < supp_card := by
        -- Since p'.val x₀ = 0, the support of p' has at least one fewer element than p
        have h_x₀_in_supp : x₀ ∈ Finset.filter (fun x => p.val x ≠ 0) Finset.univ := by
          simp [Finset.mem_filter]
          -- x₀ is chosen from the support, so p.val x₀ ≠ 0
          have hx₀_in_supp : x₀ ∈ {x | p.val x ≠ 0} := by
            have : x₀ ∈ Finset.filter (fun x => p.val x ≠ 0) Finset.univ := supp_nonempty_alt.choose_spec
            simp [Finset.mem_filter] at this
            exact this
          exact hx₀_in_supp
        have h_x₀_not_in_supp_p' : x₀ ∉ Finset.filter (fun x => p'.val x ≠ 0) Finset.univ := by
          simp [Finset.mem_filter, p']
        -- The support of p' is a subset of the support of p minus x₀
        have h_subset : Finset.filter (fun x => p'.val x ≠ 0) Finset.univ ⊆
                       (Finset.filter (fun x => p.val x ≠ 0) Finset.univ).erase x₀ := by
          intro x hx_mem_supp_p'_full
          simp only [Finset.mem_filter, Finset.mem_erase] at hx_mem_supp_p'_full ⊢
          -- hx_mem_supp_p'_full is (x ∈ Finset.univ ∧ p'.val x ≠ 0)
          -- ⊢ is (x ≠ x₀ ∧ x ∈ Finset.univ ∧ p.val x ≠ 0)
          rcases hx_mem_supp_p'_full with ⟨hx_univ, hp'_val_x_ne_zero⟩
          constructor
          · -- Goal 1: x ≠ x₀
            by_cases h_x_eq_x₀ : x = x₀
            · -- Case x = x₀.
              rw [h_x_eq_x₀] at hp'_val_x_ne_zero
              simp [p'] at hp'_val_x_ne_zero
            · -- Case x ≠ x₀.
              exact h_x_eq_x₀
          · -- Goal 2: x ∈ Finset.univ ∧ p.val x ≠ 0
            constructor
            · -- Goal 2.1: x ∈ Finset.univ
              exact hx_univ
            · -- Goal 2.2: p.val x ≠ 0
              by_cases h_x_eq_x₀ : x = x₀
              · -- Case x = x₀.
                rw [h_x_eq_x₀] at hp'_val_x_ne_zero
                simp [p'] at hp'_val_x_ne_zero
              · -- Case x ≠ x₀.
                intro h_p_val_x_eq_zero -- Assume p.val x = 0
                have h_p'_val_x_is_zero : p'.val x = 0 := by
                  simp [p', h_x_eq_x₀, h_p_val_x_eq_zero, zero_div]
                exact hp'_val_x_ne_zero h_p'_val_x_is_zero
        calc Finset.card (Finset.filter (fun x => p'.val x ≠ 0) Finset.univ)
            ≤ Finset.card ((Finset.filter (fun x => p.val x ≠ 0) Finset.univ).erase x₀) := Finset.card_le_card h_subset
          _ = Finset.card (Finset.filter (fun x => p.val x ≠ 0) Finset.univ) - 1 := by
              rw [Finset.card_erase_of_mem h_x₀_in_supp]
          _ < Finset.card (Finset.filter (fun x => p.val x ≠ 0) Finset.univ) := by
              rw [hk_eq_k]
              apply Nat.sub_lt (by linarith [h_supp_card_gt_1]) (by norm_num)

      have h_ind_p' := (h_ind_hyp (Finset.card (Finset.filter (fun x => p'.val x ≠ 0) Finset.univ)) (lt_of_lt_of_le (hk_eq_k ▸ h_supp_p'_lt) hk_le_k_max)) (Finset.card (Finset.filter (fun x => p'.val x ≠ 0) Finset.univ)) (le_refl _) p' rfl
      have h_δx₀_sim := h_delta_sim_L_ux x₀

      -- Define this helper lemma first to make the proof cleaner
      have h_EU_delta_x₀ : expectedUtility (δ x₀) u = u x₀ := by
        unfold expectedUtility
        simp [δ, Finset.sum_ite_eq', Finset.mem_univ, if_true]

      have h_EU_p_eq_mix_EU : expectedUtility p u = α₀ * expectedUtility (δ x₀) u + (1 - α₀) * expectedUtility p' u := by
        conv_lhs => unfold expectedUtility
        rw [h_p_eq_mix_val]
        simp only [Lottery.mix]

        -- Split into cases based on x = x₀ or x ≠ x₀
        have h_split : ∑ x ∈ Finset.filter (fun x => α₀ * (δ x₀).val x + (1 - α₀) * p'.val x ≠ 0) Finset.univ,
                       (α₀ * (δ x₀).val x + (1 - α₀) * p'.val x) * u x =
                       ∑ x ∈ Finset.filter (fun x => x = x₀) Finset.univ,
                         (α₀ * (δ x₀).val x + (1 - α₀) * p'.val x) * u x +
                       ∑ x ∈ Finset.filter (fun x => x ≠ x₀ ∧ p'.val x ≠ 0) Finset.univ,
                         (α₀ * (δ x₀).val x + (1 - α₀) * p'.val x) * u x := by
          -- This is true because we need to account for all non-zero terms
          -- We'll prove this by showing the two sets partition the non-zero terms
          rw [← Finset.sum_union]
          · congr 1
            ext x
            simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
            constructor
            · intro h_nonzero
              by_cases hx : x = x₀
              · left; exact hx
              · right
                constructor
                · exact hx
                · by_contra h_p'_zero
                  simp [δ, hx, h_p'_zero] at h_nonzero
            · intro h
              cases h with
              | inl h_eq =>
                rw [h_eq]
                simp [δ, p']
                exact ne_of_gt h_α₀_pos
              | inr h_and =>
                simp [δ, h_and.1]
                constructor
                · exact ne_of_gt (sub_pos_of_lt h_α₀_lt_1)
                · exact h_and.2
          · -- Prove disjointness
            simp only [Finset.disjoint_iff_ne]
            intros a ha b hb
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
            intro h_eq
            rw [← h_eq] at hb
            exact hb.1 ha

        -- Calculate each part separately
        rw [h_split]
        have h1 : ∑ x ∈ Finset.filter (fun x => x = x₀) Finset.univ,
                  (α₀ * (δ x₀).val x + (1 - α₀) * p'.val x) * u x = α₀ * u x₀ := by
          rw [Finset.sum_filter]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
          simp [δ, p']

        have h2 : ∑ x ∈ Finset.filter (fun x => x ≠ x₀ ∧ p'.val x ≠ 0) Finset.univ,
                  (α₀ * (δ x₀).val x + (1 - α₀) * p'.val x) * u x =
                  (1 - α₀) * ∑ x ∈ Finset.filter (fun x => p'.val x ≠ 0) Finset.univ, p'.val x * u x := by
          -- First simplify using the fact that δ x₀ x = 0 when x ≠ x₀
          have h_simplify : ∀ x ∈ Finset.filter (fun x => x ≠ x₀ ∧ p'.val x ≠ 0) Finset.univ,
                           (α₀ * (δ x₀).val x + (1 - α₀) * p'.val x) * u x = (1 - α₀) * p'.val x * u x := by
            intro x hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
            have : (δ x₀).val x = 0 := by simp [δ, if_neg hx.1]
            simp [this]
          rw [Finset.sum_congr rfl h_simplify]
          -- Factor out (1 - α₀) from the sum
          simp_rw [mul_assoc] -- Change ((1-α₀)*p'.val x)*u x to (1-α₀)*(p'.val x * u x)
          rw [Finset.mul_sum]  -- Apply ∑ c*f x = c * ∑ f x
          congr 1
          -- We need to show the filter sets are equal
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro ⟨hx_ne, hp'_ne⟩
            exact hp'_ne
          · intro hp'_ne
            constructor
            · -- Need to show x ≠ x₀
              by_contra hx_eq
              rw [hx_eq] at hp'_ne
              simp [p'] at hp'_ne
            · exact hp'_ne

        -- Combine the parts and simplify
        rw [h1, h2, h_EU_delta_x₀]
        unfold expectedUtility -- Unfold the remaining expectedUtility p' u on RHS
        ring

      -- The goal is already about Lottery.mix (δ x₀) p' α₀, which equals p by h_p_eq_mix_val
      -- We need to show this mix is indifferent to L_mix of its expected utility
      -- Since p = Lottery.mix (δ x₀) p' α₀, we have:
      -- (Lottery.mix (δ x₀) p' α₀).expectedUtility u = p.expectedUtility u
      have h_mix_EU_eq_p_EU : expectedUtility (@Lottery.mix X _ (δ x₀) p' α₀ (le_of_lt h_α₀_pos) h_α₀_le_1) u = expectedUtility p u := by
        congr 1
        exact Subtype.eq h_p_eq_mix_val.symm

      -- First, let's establish the expected utility equality we need
      have h_EU_mix_expanded : expectedUtility (@Lottery.mix X _ (δ x₀) p' α₀ (le_of_lt h_α₀_pos) h_α₀_le_1) u = α₀ * u x₀ + (1 - α₀) * expectedUtility p' u := by
        rw [h_mix_EU_eq_p_EU, h_EU_p_eq_mix_EU]
        rw [show expectedUtility (δ x₀) u = u x₀ by simp [expectedUtility, δ, Finset.sum_ite_eq', Finset.mem_univ, if_true]]


      -- By the induction hypothesis, p' ~ L_mix (expectedUtility p' u) _ _
      -- And we know δ x₀ ~ L_mix (u x₀) _ _
      -- So we can use independence to show the mix is indifferent to L_mix of its expected utility

      let L_δx₀ := L_mix (u x₀) (h_u_bounds x₀).1 (h_u_bounds x₀).2
      let L_p' := L_mix (expectedUtility p' u) (h_EU_bounds p').1 (h_EU_bounds p').2

      -- Step 1: Show Lottery.mix (δ x₀) p' α₀ ~ Lottery.mix L_δx₀ p' α₀
      have h_step1 : @Lottery.mix X _ (δ x₀) p' α₀ (le_of_lt h_α₀_pos) h_α₀_le_1 ~
                     @Lottery.mix X _ L_δx₀ p' α₀ (le_of_lt h_α₀_pos) h_α₀_le_1 := by
        have h_α_cond : 0 < α₀ ∧ α₀ ≤ 1 := ⟨h_α₀_pos, h_α₀_le_1⟩
        exact PrefRel.indep_indiff (δ x₀) L_δx₀ p' α₀ h_α_cond h_δx₀_sim

      -- Step 2: Show Lottery.mix L_δx₀ p' α₀ ~ Lottery.mix L_δx₀ L_p' α₀
      have h_step2 : @Lottery.mix X _ L_δx₀ p' α₀ (le_of_lt h_α₀_pos) h_α₀_le_1 ~
                     @Lottery.mix X _ L_δx₀ L_p' α₀ (le_of_lt h_α₀_pos) h_α₀_le_1 := by
        -- We need to use independence with 1-α₀
        have h_1_minus_α₀_pos : 0 < 1 - α₀ := by linarith [h_α₀_lt_1]
        have h_1_minus_α₀_le_1 : 1 - α₀ ≤ 1 := by linarith [h_α₀_pos]
        have h_cond : 0 < 1 - α₀ ∧ 1 - α₀ ≤ 1 := ⟨h_1_minus_α₀_pos, h_1_minus_α₀_le_1⟩
        -- Apply independence to get mix p' L_δx₀ (1-α₀) ~ mix L_p' L_δx₀ (1-α₀)
        have h_ind := PrefRel.indep_indiff p' L_p' L_δx₀ (1-α₀) h_cond h_ind_p'
        -- Now we need to show these are equal to our mixes
        have h_eq1 : @Lottery.mix X _ p' L_δx₀ (1-α₀) (le_of_lt h_1_minus_α₀_pos) h_1_minus_α₀_le_1 =
                     @Lottery.mix X _ L_δx₀ p' α₀ (le_of_lt h_α₀_pos) h_α₀_le_1 := by
          apply Subtype.eq; ext x; simp [Lottery.mix]; ring
        have h_eq2 : @Lottery.mix X _ L_p' L_δx₀ (1-α₀) (le_of_lt h_1_minus_α₀_pos) h_1_minus_α₀_le_1 =
                     @Lottery.mix X _ L_δx₀ L_p' α₀ (le_of_lt h_α₀_pos) h_α₀_le_1 := by
          apply Subtype.eq; ext x; simp [Lottery.mix]; ring
        -- Transform h_ind using the equalities
        unfold indiff at h_ind ⊢
        constructor
        · -- First part: L_δx₀ p' α₀ ≿ L_δx₀ L_p' α₀
          rw [←h_eq1, ←h_eq2]
          exact h_ind.1
        · -- Second part: L_δx₀ L_p' α₀ ≿ L_δx₀ p' α₀
          rw [←h_eq1, ←h_eq2]
          exact h_ind.2

      -- Step 3: Combine by transitivity
      have h_combined : @Lottery.mix X _ (δ x₀) p' α₀ (le_of_lt h_α₀_pos) h_α₀_le_1 ~
                        @Lottery.mix X _ L_δx₀ L_p' α₀ (le_of_lt h_α₀_pos) h_α₀_le_1 := by
        unfold indiff at h_step1 h_step2 ⊢
        apply And.intro
        · exact PrefRel.transitive _ _ _ h_step1.1 h_step2.1
        · exact PrefRel.transitive _ _ _ h_step2.2 h_step1.2

      -- Step 4: Show that Lottery.mix L_δx₀ L_p' α₀ equals L_mix of the expected utility
      have h_final_eq : @Lottery.mix X _ L_δx₀ L_p' α₀ (le_of_lt h_α₀_pos) h_α₀_le_1 =
                        L_mix (expectedUtility p u) (h_EU_bounds p).1 (h_EU_bounds p).2 := by
        apply Subtype.eq; ext x
        simp [Lottery.mix, L_mix, Lottery.mix, L_δx₀, L_p']
        -- Need to show the values are equal
        -- L_mix constructs a lottery that equals p_star with probability EU and p_circ with probability 1-EU
        -- We need to use the fact that EU(p) = α₀ * u(x₀) + (1-α₀) * EU(p')
        rw [h_EU_p_eq_mix_EU, h_EU_delta_x₀]
        -- The mixed lottery should distribute the same way
        -- We need to show that for each x, the lottery values are equal
        -- The goal is about mixing p_star and p_circ with appropriate probabilities

        -- First, let's understand what L_mix does:
        -- L_mix γ creates a lottery that is γ*p_star + (1-γ)*p_circ

        -- On the LHS, we have:
        -- α₀ * (u x₀ * p_star.val x + (1 - u x₀) * p_circ.val x) +
        -- (1 - α₀) * (expectedUtility p' u * p_star.val x + (1 - expectedUtility p' u) * p_circ.val x)

        -- On the RHS, we have:
        -- (α₀ * u x₀ + (1 - α₀) * expectedUtility p' u) * p_star.val x +
        -- (1 - (α₀ * u x₀ + (1 - α₀) * expectedUtility p' u)) * p_circ.val x

        -- These are equal by distributivity
        ring

      -- Final step: use the equality to transfer the indifference
      rw [h_final_eq] at h_combined
      -- We need to show that p = Lottery.mix (δ x₀) p' α₀ to apply h_combined
      have h_p_eq : p = @Lottery.mix X _ (δ x₀) p' α₀ (le_of_lt h_α₀_pos) h_α₀_le_1 :=
        Subtype.eq h_p_eq_mix_val
      -- h_combined already shows what we need, just need to convert the bounds
      -- We have h_combined : Lottery.mix (δ x₀) p' α₀ ~ L_mix (p.expectedUtility u) (h_EU_bounds p).1 (h_EU_bounds p).2
      -- We need: Lottery.mix (δ x₀) p' α₀ ~ L_mix ((Lottery.mix (δ x₀) p' α₀).expectedUtility u) ⋯ ⋯
      -- Since (Lottery.mix (δ x₀) p' α₀).expectedUtility u = p.expectedUtility u by h_mix_EU_eq_p_EU
      -- We can use the fact that L_mix with the same value gives the same lottery
      have h_L_mix_eq : L_mix (expectedUtility (@Lottery.mix X _ (δ x₀) p' α₀ (le_of_lt h_α₀_pos) h_α₀_le_1) u)
                               (h_EU_bounds (@Lottery.mix X _ (δ x₀) p' α₀ (le_of_lt h_α₀_pos) h_α₀_le_1)).1
                               (h_EU_bounds (@Lottery.mix X _ (δ x₀) p' α₀ (le_of_lt h_α₀_pos) h_α₀_le_1)).2 =
                        L_mix (expectedUtility p u) (h_EU_bounds p).1 (h_EU_bounds p).2 := by
        congr 1
      rw [h_L_mix_eq]
      exact h_combined
  } -- Closes the `by {` block for `h_p_sim_L_EU_p`

  -- Final step: Prove p ≿ q ⟺ EU p u ≥ EU q u
  intro p q
  let α_eu := expectedUtility p u
  let β_eu := expectedUtility q u
  let L_α := L_mix α_eu (h_EU_bounds p).1 (h_EU_bounds p).2
  let L_β := L_mix β_eu (h_EU_bounds q).1 (h_EU_bounds q).2
  have h_p_sim_Lα : p ~ L_α := h_p_sim_L_EU_p p
  have h_q_sim_Lβ : q ~ L_β := h_p_sim_L_EU_p q

  constructor
  · intro hpq_assum -- Assume p ≿ q, show α_eu ≥ β_eu
    have h_Lα_pref_Lβ : L_α ≿ L_β := by
      -- We have p ~ L_α, p ≿ q, and q ~ L_β
      -- We want to show L_α ≿ L_β
      -- First: L_α ~ p (by symmetry of h_p_sim_Lα)
      -- Second: p ≿ q (given as hpq_assum)
      -- Third: q ~ L_β (given as h_q_sim_Lβ)
      -- So: L_α ≿ p ≿ q ≿ L_β
      have h_Lα_pref_p : L_α ≿ p := (indiff_symmetric _ _ h_p_sim_Lα).1
      have h_p_pref_q : p ≿ q := hpq_assum
      have h_q_pref_Lβ : q ≿ L_β := h_q_sim_Lβ.1
      exact PrefRel.transitive L_α q L_β (PrefRel.transitive L_α p q h_Lα_pref_p h_p_pref_q) h_q_pref_Lβ
    by_contra h_contr
    rw [not_le] at h_contr -- α_eu < β_eu
    unfold u at h_contr
    by_cases h_ps_sim_pc_contra : p_star ~ p_circ
    · -- p_star ~ p_circ case. u x = 0. So α_eu = 0, β_eu = 0. Contradicts α_eu < β_eu.
      simp only [if_pos h_ps_sim_pc_contra] at h_contr
      -- When u is the zero function, both expected utilities are 0
      have h_α_eu_zero : α_eu = 0 := by
        unfold α_eu expectedUtility
        simp [u, h_ps_sim_pc_contra, mul_zero, Finset.sum_const_zero]
      have h_β_eu_zero : β_eu = 0 := by
        unfold β_eu expectedUtility
        simp [u, h_ps_sim_pc_contra, mul_zero, Finset.sum_const_zero]
      -- We have α_eu = 0 and β_eu = 0, but h_contr says α_eu < β_eu
      -- This means 0 < 0, which is a contradiction
      have h_contradiction : (0 : Real) < 0 := by
        have h_α_eq : expectedUtility p u = α_eu := rfl
        have h_β_eq : expectedUtility q u = β_eu := rfl
        rw [h_α_eq, h_β_eq] at h_contr
        rw [h_α_eu_zero, h_β_eu_zero] at h_contr
        exact h_contr
      exact lt_irrefl 0 h_contradiction
    · -- p_star ≻ p_circ case.
      simp only [if_neg h_ps_sim_pc_contra] at h_contr
      let h_ps_succ_pc : p_star ≻ p_circ := by
        unfold strictPref
        constructor
        · exact h_p_star_is_max x_circ
        · unfold indiff at h_ps_sim_pc_contra
          push_neg at h_ps_sim_pc_contra
          -- We have h_ps_sim_pc_contra : (p_star ≿ p_circ) → ¬p_circ ≿ p_star
          -- We know p_star ≿ p_circ from h_p_star_is_max x_circ
          -- So we can apply h_ps_sim_pc_contra to get ¬p_circ ≿ p_star
          exact h_ps_sim_pc_contra (h_p_star_is_max x_circ)
      have h_Lβ_succ_Lα := claim_ii α_eu β_eu h_ps_succ_pc (h_EU_bounds p).1 h_contr (h_EU_bounds q).2
      exact h_Lβ_succ_Lα.2 h_Lα_pref_Lβ
  · intro h_α_ge_β -- Assume α_eu ≥ β_eu, show p ≿ q
    -- We have p ~ L_α and q ~ L_β
    -- We want to show p ≿ q given α_eu ≥ β_eu
    -- Strategy: Show L_α ≿ L_β, then use transitivity with the indifferences

    have h_Lα_pref_Lβ : L_α ≿ L_β := by
      -- We need to show that L_mix α_eu ≿ L_mix β_eu when α_eu ≥ β_eu
      -- This follows from the fact that these are mixtures of p_star and p_circ
      -- with p_star ≿ p_circ, and higher mixture coefficients preserve preference

      by_cases h_eq : α_eu = β_eu
      · -- If α_eu = β_eu, then L_α = L_β
        have h_Lα_eq_Lβ : L_α = L_β := by
          unfold L_α L_β
          congr 1
        rw [h_Lα_eq_Lβ]
        exact PrefRel.refl L_β
      · -- If α_eu ≠ β_eu and α_eu ≥ β_eu, then α_eu > β_eu
        have h_α_gt_β : α_eu > β_eu := lt_of_le_of_ne h_α_ge_β (Ne.symm h_eq)

        by_cases h_ps_sim_pc : p_star ~ p_circ
        · -- If p_star ~ p_circ, then u is the zero function
          have h_α_eu_zero : α_eu = 0 := by
            unfold α_eu expectedUtility u
            simp [h_ps_sim_pc, mul_zero, Finset.sum_const_zero]
          have h_β_eu_zero : β_eu = 0 := by
            unfold β_eu expectedUtility u
            simp [h_ps_sim_pc, mul_zero, Finset.sum_const_zero]
          -- This contradicts α_eu > β_eu
          rw [h_α_eu_zero, h_β_eu_zero] at h_α_gt_β
          exact False.elim (lt_irrefl 0 h_α_gt_β)
        · -- If p_star ≻ p_circ
          let h_ps_succ_pc : p_star ≻ p_circ := by
            unfold strictPref
            constructor
            · exact h_p_star_is_max x_circ
            · intro h_circ_pref_star
              apply h_ps_sim_pc
              unfold indiff
              exact ⟨h_p_star_is_max x_circ, h_circ_pref_star⟩

          -- Use claim_ii: if p_star ≻ p_circ and β_eu < α_eu, then L_α ≻ L_β
          have h_Lα_succ_Lβ := claim_ii β_eu α_eu h_ps_succ_pc (h_EU_bounds q).1 h_α_gt_β (h_EU_bounds p).2
          exact h_Lα_succ_Lβ.1

    -- Now use transitivity: p ~ L_α ≿ L_β ~ q implies p ≿ q
    apply PrefRel.transitive p L_α q
    · exact h_p_sim_Lα.1  -- p ≿ L_α
    · apply PrefRel.transitive L_α L_β q
      · exact h_Lα_pref_Lβ  -- L_α ≿ L_β
      · exact (indiff_symmetric q L_β h_q_sim_Lβ).1  -- L_β ≿ q
