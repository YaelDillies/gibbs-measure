/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {C : Set (Set α)} {μ ν : Measure α}

namespace Measure

lemma ext_of_generateFrom_of_univ
    (hA : ‹MeasurableSpace α› = MeasurableSpace.generateFrom C) (hC : IsPiSystem C)
    (h_univ : (univ : Set α) ∈ C) (hμ : μ univ ≠ ∞)
    (h : ∀ s ∈ C, μ s = ν s) : μ = ν :=
  ext_of_generateFrom_of_iUnion C (fun _ ↦ univ) hA hC (iUnion_const univ)
    (fun _ ↦ h_univ) (fun _ ↦ hμ) h

end Measure

lemma ext_of_generate_finite_of_isProbabilityMeasure
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hA : ‹MeasurableSpace α› = MeasurableSpace.generateFrom C) (hC : IsPiSystem C)
    (hμν : ∀ s ∈ C, μ s = ν s) : μ = ν :=
  ext_of_generate_finite C hA hC hμν (by simp)

end MeasureTheory
