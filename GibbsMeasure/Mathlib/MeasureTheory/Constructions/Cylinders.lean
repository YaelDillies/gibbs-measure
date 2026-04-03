module

public import Mathlib.MeasureTheory.Constructions.Cylinders

open MeasureTheory Set

variable {S E : Type*} {mE : MeasurableSpace E}

public lemma mem_congr_of_measurableSet_cylinderEvents {Δ : Set S} {B : Set (S → E)}
    (hB : MeasurableSet[cylinderEvents Δ] B) {f₁ f₂ : S → E} (h : ∀ i ∈ Δ, f₁ i = f₂ i) :
    f₁ ∈ B ↔ f₂ ∈ B := by
  unfold cylinderEvents at hB
  rw [MeasurableSpace.measurableSet_iSup] at hB
  refine hB.recOn (fun s ⟨i,hi⟩ ↦ ?_) (by simp) (fun _ _ ih => ih.not) (fun _ _ ih ↦ by simp [ih])
  by_cases hiΔ : i ∈ Δ
  · rw [iSup_pos hiΔ, MeasurableSpace.measurableSet_comap] at hi
    obtain ⟨_ , _, rfl⟩ := hi
    simp only [mem_preimage, h i hiΔ]
  · rw [iSup_neg hiΔ, MeasurableSpace.measurableSet_bot_iff] at hi
    rcases hi with rfl | rfl <;> exact iff_of_eq rfl
