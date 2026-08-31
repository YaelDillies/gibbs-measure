module

public import GibbsMeasure.Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.Measure.Map

public section

open MeasureTheory Set

section juxt
variable {S E : Type*} {𝓔 : MeasurableSpace E} {Λ s : Set S} {t : S → Set E} {η : S → E} {x : S}

noncomputable def juxt (Λ : Set S) (η : S → E) (ζ : Λ → E) (x : S) : E := by
  classical exact dite (x ∈ Λ) (fun h ↦ ζ ⟨x, h⟩) (fun _ ↦ η x)

@[simp]
lemma juxt_apply_of_mem (hx : x ∈ Λ) (ζ : Λ → E) : juxt Λ η ζ x = ζ ⟨x, hx⟩ := by simp [juxt, hx]

@[simp]
lemma juxt_apply_of_not_mem (h : x ∉ Λ) (ζ : Λ → E) : juxt Λ η ζ x = η x := by simp [juxt, h]

protected lemma Measurable.juxt : Measurable (juxt Λ η) := by
  rw [measurable_pi_iff]
  rintro x
  by_cases hx : x ∈ Λ <;> simp [juxt, hx, measurable_pi_apply]

lemma preimage_juxt_pi [DecidablePred (· ∈ s)] (hη : η ∈ (s \ Λ).pi t) :
    juxt Λ η ⁻¹' s.pi t = univ.pi fun j : Λ ↦ if (j : S) ∈ s then t j else univ := by
  ext ζ
  simp only [mem_preimage, mem_pi]
  refine ⟨fun h j ↦ ?_, fun h i hi ↦ ?_⟩
  · split_ifs with hjs
    · simpa [juxt_apply_of_mem j.property] using h _ hjs
    · simp
  · by_cases hiΛ : i ∈ Λ
    · simpa [juxt_apply_of_mem hiΛ, hi] using h ⟨i, hiΛ⟩
    · simpa [juxt_apply_of_not_mem hiΛ] using hη i ⟨hi, hiΛ⟩

lemma preimage_juxt_pi_eq_empty (hη : η ∉ (s \ Λ).pi t) :
    juxt Λ η ⁻¹' s.pi t = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro ζ hζ
  simp only [mem_preimage, mem_pi] at hζ hη
  push Not at hη
  obtain ⟨i, ⟨his, hiΛ⟩, hit⟩ := hη
  exact hit <| by simpa [juxt_apply_of_not_mem hiΛ] using hζ i his

lemma map_juxt_pi [DecidablePred (· ∈ s)] (μ : Measure (Λ → E))
    (ht : ∀ i, MeasurableSet (t i)) (hs : s.Countable) (η : S → E) :
    μ.map (juxt Λ η) (s.pi t) =
      ((s \ Λ).pi t).indicator
        (fun _ ↦ μ (univ.pi fun j : Λ ↦ if (j : S) ∈ s then t j else univ)) η := by
  rw [Measure.map_apply .juxt (MeasurableSet.pi hs fun i _ ↦ ht i)]
  by_cases hη : η ∈ (s \ Λ).pi t
  · rw [preimage_juxt_pi hη, indicator_of_mem hη]
  · rw [preimage_juxt_pi_eq_empty hη, measure_empty, indicator_of_notMem hη]

lemma measurable_map_juxt_pi (μ : Measure (Λ → E)) (ht : ∀ i, MeasurableSet (t i))
    (hs : s.Countable) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) Λᶜ] fun η : S → E ↦
      μ.map (juxt Λ η) (s.pi t) := by
  classical
  simp_rw [map_juxt_pi μ ht hs]
  exact Measurable.indicator measurable_const
    (MeasurableSet.pi_cylinderEvents (fun _ h ↦ h.2) (hs.mono sdiff_subset) fun i _ ↦ ht i)

end juxt
