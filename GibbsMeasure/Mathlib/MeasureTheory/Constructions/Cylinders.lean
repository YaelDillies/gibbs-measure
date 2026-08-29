/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.Function.FactorsThrough

@[expose] public section

open Function MeasureTheory Set

variable {S E : Type*} {mE : MeasurableSpace E}

lemma mem_congr_of_measurableSet_cylinderEvents {Δ : Set S} {B : Set (S → E)}
    (hB : MeasurableSet[cylinderEvents Δ] B) {f₁ f₂ : S → E} (h : ∀ i ∈ Δ, f₁ i = f₂ i) :
    f₁ ∈ B ↔ f₂ ∈ B := by
  unfold cylinderEvents at hB
  rw [MeasurableSpace.measurableSet_iSup] at hB
  refine hB.recOn (fun s ⟨i, hi⟩ ↦ ?_) (by simp) (fun _ _ ih ↦ ih.not) (fun _ _ ih ↦ by simp [ih])
  by_cases hiΔ : i ∈ Δ
  · rw [iSup_pos hiΔ, MeasurableSpace.measurableSet_comap] at hi
    obtain ⟨_, _, rfl⟩ := hi
    simp only [mem_preimage, h i hiΔ]
  · rw [iSup_neg hiΔ, MeasurableSpace.measurableSet_bot_iff] at hi
    rcases hi with rfl | rfl <;> exact iff_of_eq rfl

namespace MeasureTheory

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] {Δ : Set ι}

lemma cylinderEvents_eq_comap_domRestrict (Δ : Set ι) :
    cylinderEvents (X := X) Δ =
      MeasurableSpace.comap Δ.domRestrict (inferInstance : MeasurableSpace (∀ i : Δ, X i)) := by
  refine le_antisymm (iSup₂_le fun i hi ↦ ?_)
    (measurable_restrict_cylinderEvents (X := X) Δ).comap_le
  exact MeasurableSpace.comap_le_comap_of_eq_comp (fun x : ∀ i : Δ, X i ↦ x ⟨i, hi⟩)
    (measurable_pi_apply _) rfl

lemma cylinderEvents_eq_comap_finsetRestrict (Λ : Finset ι) :
    cylinderEvents (X := X) (Λ : Set ι) =
      MeasurableSpace.comap (Λ.restrict (π := X))
        (inferInstance : MeasurableSpace (Π i : Λ, X i)) :=
  cylinderEvents_eq_comap_domRestrict (X := X) (Λ : Set ι)

variable {Z : Type*} [MeasurableSpace Z] {f : (∀ i, X i) → Z}

theorem _root_.Measurable.dependsOn_of_cylinderEvents [MeasurableSingletonClass Z]
    (hf : Measurable[cylinderEvents Δ] f) : DependsOn f Δ :=
  dependsOn_iff_factorsThrough.2 <| by
    rw [cylinderEvents_eq_comap_domRestrict] at hf
    exact hf.factorsThrough

theorem _root_.Measurable.cylinderEvents_of_dependsOn
    (hf : Measurable f) (hdep : DependsOn f Δ) : Measurable[cylinderEvents Δ] f := by
  rcases isEmpty_or_nonempty (∀ i, X i) with hα | hα
  · intro s _
    convert MeasurableSet.empty
    exact eq_empty_of_isEmpty _
  · classical
    obtain ⟨x₀⟩ := hα
    let e : (∀ i : Δ, X i) → ∀ i, X i := fun y i ↦ if h : i ∈ Δ then y ⟨i, h⟩ else x₀ i
    have he : Measurable e := by
      refine measurable_pi_lambda _ fun i ↦ ?_
      by_cases h : i ∈ Δ
      · simp only [e, h, dite_true]
        exact measurable_pi_apply _
      · simp only [e, h, dite_false]
        exact measurable_const
    have hfe : f = (f ∘ e) ∘ Δ.domRestrict := by
      funext x
      refine (hdep fun i hi ↦ ?_).symm
      simp [e, hi, Set.domRestrict]
    rw [cylinderEvents_eq_comap_domRestrict, hfe]
    exact (hf.comp he).comp (Measurable.of_comap_le le_rfl)

theorem measurable_cylinderEvents_iff_dependsOn [MeasurableSingletonClass Z] :
    Measurable[cylinderEvents Δ] f ↔ Measurable f ∧ DependsOn f Δ :=
  ⟨fun h ↦ ⟨h.mono cylinderEvents_le_pi le_rfl, h.dependsOn_of_cylinderEvents⟩,
    fun h ↦ h.1.cylinderEvents_of_dependsOn h.2⟩

variable (ι) (X) in
abbrev measurableSquareCylinders : Set (Set (∀ i, X i)) :=
  squareCylinders fun _ ↦ {s | MeasurableSet s}

lemma isPiSystem_measurableSquareCylinders :
    IsPiSystem (measurableSquareCylinders ι X) :=
  isPiSystem_squareCylinders (fun _ ↦ MeasurableSpace.isPiSystem_measurableSet)
    fun _ ↦ MeasurableSet.univ

lemma generateFrom_measurableSquareCylinders :
    MeasurableSpace.generateFrom (measurableSquareCylinders ι X) = MeasurableSpace.pi :=
  generateFrom_squareCylinders

lemma univ_mem_measurableSquareCylinders :
    (univ : Set (∀ i, X i)) ∈ measurableSquareCylinders ι X :=
  ⟨∅, fun _ ↦ univ, fun _ _ ↦ MeasurableSet.univ, by simp⟩

end MeasureTheory
