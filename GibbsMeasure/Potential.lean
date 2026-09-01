/-
Copyright (c) 2026 Yaël Dillies, Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Interaction potentials

A potential is a family of real functions indexed by finite subsets of the site set.
`IsPotential` is cylinder-measurability of each term; `IsFiniteRange` is locally finite support.
-/

@[expose] public section

open Set Finset MeasureTheory

variable {S E : Type*}

/-- A (multi-body) interaction potential. -/
abbrev Potential (S E : Type*) :=
  (Δ : Finset S) → (S → E) → ℝ

namespace Potential

variable {Φ : Potential S E}

/-- Each term `Φ Δ` is measurable for the cylinder σ-algebra on `Δ`. -/
class IsPotential [MeasurableSpace E] (Φ : Potential S E) : Prop where
  measurable (Δ : Finset S) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) (Δ : Set S)] (Φ Δ)

/-- Each site belongs to only finitely many interacting supports. -/
class IsFiniteRange (Φ : Potential S E) : Prop where
  finite (i : S) : {A : Finset S | i ∈ A ∧ Φ A ≠ 0}.Finite

lemma IsFiniteRange.exists_finset (Φ : Potential S E) [IsFiniteRange Φ] (i : S) :
    ∃ Δ : Finset S, ∀ A : Finset S, i ∈ A → Φ A ≠ 0 → A ⊆ Δ := by
  classical
  exact ⟨(IsFiniteRange.finite (Φ := Φ) i).toFinset.sup id, fun A hi hΦ ↦
    Finset.le_sup (f := id) (by simp [hi, hΦ])⟩

lemma IsFiniteRange.finite_support (Φ : Potential S E) [IsFiniteRange Φ] (Λ : Finset S) :
    ({Δ : Finset S | ¬ Disjoint Δ Λ ∧ Φ Δ ≠ 0} : Set (Finset S)).Finite :=
  (Λ.finite_toSet.biUnion fun i _ ↦ IsFiniteRange.finite (Φ := Φ) i).subset fun A ⟨hA, hΦ⟩ ↦ by
    obtain ⟨x, hxA, hxΛ⟩ := not_disjoint_iff.1 hA
    exact mem_biUnion (Finset.mem_coe.2 hxΛ) ⟨hxA, hΦ⟩

/-- Interaction supports that meet `Λ` and carry a nonzero term. -/
noncomputable def interactingSupport [IsFiniteRange Φ] (Λ : Finset S) : Finset (Finset S) :=
  (IsFiniteRange.finite_support (Φ := Φ) Λ).toFinset

lemma mem_interactingSupport [IsFiniteRange Φ] {Λ Δ : Finset S} :
    Δ ∈ interactingSupport (Φ := Φ) Λ ↔ ¬ Disjoint Δ Λ ∧ Φ Δ ≠ 0 := by
  simp [interactingSupport]

lemma interactingSupport_subset_of_subset [IsFiniteRange Φ] {Λ₁ Λ₂ : Finset S} (hΛ : Λ₁ ⊆ Λ₂) :
    interactingSupport (Φ := Φ) Λ₁ ⊆ interactingSupport (Φ := Φ) Λ₂ := by
  intro Δ hΔ
  rw [mem_interactingSupport] at hΔ ⊢
  exact ⟨mt (Disjoint.mono_right hΛ) hΔ.1, hΔ.2⟩

/-- Finite sum of the interaction terms whose support meets `Λ`. -/
noncomputable def interactingHamiltonian [IsFiniteRange Φ] (Λ : Finset S) (η : S → E) : ℝ :=
  ∑ Δ ∈ interactingSupport (Φ := Φ) Λ, Φ Δ η

section Truncation
open Classical

/-- Truncation of `Φ` to interactions contained in `Δ`. -/
noncomputable def truncation (Φ : Potential S E) (Δ : Finset S) : Potential S E :=
  fun A η ↦ if A ⊆ Δ then Φ A η else 0

@[simp] lemma truncation_of_subset {Δ B : Finset S} (h : B ⊆ Δ) :
    Φ.truncation Δ B = Φ B := funext fun _ ↦ if_pos h

@[simp] lemma truncation_of_not_subset {Δ B : Finset S} (h : ¬ B ⊆ Δ) :
    Φ.truncation Δ B = 0 := funext fun _ ↦ if_neg h

instance (Δ : Finset S) : IsFiniteRange (Φ.truncation Δ) where
  finite i := (Δ.powerset.finite_toSet).subset fun A hA ↦
    mem_powerset.2 <| by_contra fun h ↦ hA.2 (truncation_of_not_subset h)

end Truncation

section
variable [MeasurableSpace E]

lemma IsPotential.dependsOn [IsPotential Φ] (Δ : Finset S) :
    DependsOn (Φ Δ) (Δ : Set S) :=
  (IsPotential.measurable (Φ := Φ) Δ).dependsOn_of_cylinderEvents

lemma IsPotential.eq_of_eqOn [IsPotential Φ] {Δ : Finset S} {η ζ : S → E}
    (h : EqOn η ζ (Δ : Set S)) : Φ Δ η = Φ Δ ζ :=
  IsPotential.dependsOn (Φ := Φ) Δ h

@[fun_prop]
lemma measurable_interactingHamiltonian [IsFiniteRange Φ] [IsPotential Φ]
    (Λ : Finset S) : Measurable (interactingHamiltonian (Φ := Φ) Λ) :=
  Finset.measurable_sum _ fun A _ ↦
    (IsPotential.measurable (Φ := Φ) A).mono
      (cylinderEvents_le_pi (X := fun _ : S ↦ E) (Δ := (A : Set S))) le_rfl

instance (Δ : Finset S) [IsPotential Φ] : IsPotential (Φ.truncation Δ) where
  measurable B := by
    classical
    exact if h : B ⊆ Δ then truncation_of_subset h ▸ IsPotential.measurable (Φ := Φ) B
      else truncation_of_not_subset h ▸ measurable_const

end

end Potential
