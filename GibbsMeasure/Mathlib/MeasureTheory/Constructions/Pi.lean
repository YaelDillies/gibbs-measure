module

public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

open Set

namespace MeasureTheory.Measure

variable {ι α : Type*} [DecidableEq ι] [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] {s t : Finset ι}

lemma pi_pi_ite (u : ι → Set α) :
    (Measure.pi fun _ : s ↦ μ) (univ.pi fun i : s ↦ if (i : ι) ∈ t then u i else univ) =
      ∏ i ∈ t ∩ s, μ (u i) := by
  rw [pi_pi]
  simp only [apply_ite, measure_univ]
  exact (Finset.prod_attach s fun i ↦ if i ∈ t then μ (u i) else 1).trans <| by
    simp [Finset.prod_ite_mem, Finset.inter_comm]

end MeasureTheory.Measure
