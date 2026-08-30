module

public import GibbsMeasure.Mathlib.Data.Set.Prod
public import GibbsMeasure.Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.Measure.Map

public section

open MeasureTheory Set

section juxt
variable {S E : Type*} {𝓔 : MeasurableSpace E} {Λ : Set S} {η : S → E} {x : S}

noncomputable def juxt (Λ : Set S) (η : S → E) (ζ : Λ → E) (x : S) : E := by
  classical exact dite (x ∈ Λ) (fun h ↦ ζ ⟨x, h⟩) (fun _ ↦ η x)

lemma juxt_apply_of_mem (hx : x ∈ Λ) (ζ : Λ → E) : juxt Λ η ζ x = ζ ⟨x, hx⟩ := by simp [juxt, hx]
lemma juxt_apply_of_not_mem (h : x ∉ Λ) (ζ : Λ → E) : juxt Λ η ζ x = η x := by simp [juxt, h]

lemma measurable_coordinate_projection_2 {Δ : Set S} {x : S} (h : x ∈ Δ) :
    Measurable[cylinderEvents Δ] (fun σ : S → E ↦ σ x) := by
  have key : @Measurable (S → E) E (𝓔.comap fun σ ↦ σ x) _ (fun σ ↦ σ x) := by
    exact Measurable.of_comap_le fun s a ↦ a
  exact key.mono (le_iSup₂_of_le x h (fun s a ↦ a)) le_rfl

protected lemma Measurable.juxt : Measurable (juxt Λ η) := by
  rw [measurable_pi_iff]
  rintro x
  by_cases hx : x ∈ Λ <;> simp [juxt, hx, measurable_pi_apply]

end juxt

variable {S E : Type*} {𝓔 : MeasurableSpace E} {Λ s : Finset S} {t : S → Set E} {η : S → E}

lemma preimage_juxt_pi [DecidableEq S] (hP : ∀ i ∈ s, i ∉ Λ → η i ∈ t i) :
    juxt (Λ : Set S) η ⁻¹' (s : Set S).pi t =
      univ.pi fun j : Λ ↦ if (j : S) ∈ s then t j else univ := by
  ext ζ
  simp only [mem_preimage, mem_pi]
  refine ⟨fun h j ↦ ?_, fun h i hi ↦ ?_⟩
  · split_ifs with hjs
    · simpa [juxt_apply_of_mem j.property] using h _ hjs
    · simp
  · by_cases hiΛ : i ∈ (Λ : Set S)
    · have : (⟨i, hiΛ⟩ : Λ).val ∈ s := hi
      simpa [juxt_apply_of_mem hiΛ, this] using h ⟨i, hiΛ⟩
    · simpa [juxt_apply_of_not_mem hiΛ] using hP i hi hiΛ

lemma preimage_juxt_pi_eq_empty (hP : ¬ ∀ i ∈ s, i ∉ Λ → η i ∈ t i) :
    juxt (Λ : Set S) η ⁻¹' (s : Set S).pi t = (∅ : Set (Λ → E)) := by
  ext ζ
  simp only [mem_preimage, mem_empty_iff_false, iff_false, mem_pi]
  intro h
  push Not at hP
  obtain ⟨i, his, hiΛ, hit⟩ := hP
  exact hit <| by simpa [juxt_apply_of_not_mem hiΛ] using h i his

lemma map_juxt_apply_pi [DecidableEq S] (μ : Measure (Λ → E)) (ht : ∀ i, MeasurableSet (t i))
    (η : S → E) :
    μ.map (juxt Λ η) ((s : Set S).pi t) =
      {ω : S → E | ∀ i ∈ s, i ∉ Λ → ω i ∈ t i}.indicator
        (fun _ ↦ μ (univ.pi fun j : Λ ↦ if (j : S) ∈ s then t j else univ)) η := by
  rw [Measure.map_apply .juxt (MeasurableSet.pi s.countable_toSet fun i _ ↦ ht i)]
  by_cases hP : ∀ i ∈ s, i ∉ Λ → η i ∈ t i
  · rw [preimage_juxt_pi hP, indicator_of_mem (mem_ofPred.2 hP)]
  · rw [preimage_juxt_pi_eq_empty hP, measure_empty, indicator_of_notMem (mem_ofPred.not.2 hP)]

lemma measurable_map_juxt_apply_pi (μ : Measure (Λ → E)) (ht : ∀ i, MeasurableSet (t i)) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)ᶜ] fun η : S → E ↦
      μ.map (juxt Λ η) ((s : Set S).pi t) := by
  classical
  simp_rw [map_juxt_apply_pi μ ht]
  exact Measurable.indicator measurable_const
    (by simpa [setOf_forall_notMem_eq_pi_sdiff] using
      (MeasurableSet.pi_cylinderEvents (X := fun _ : S ↦ E) (s := s \ Λ)
        (fun i hi ↦ mem_compl (Finset.mem_sdiff.1 hi).2) fun i _ ↦ ht i))
