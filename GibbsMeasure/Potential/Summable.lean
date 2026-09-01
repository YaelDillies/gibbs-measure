/-
Copyright (c) 2026 Yaël Dillies, Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Matteo Cipollina
-/
module

public import GibbsMeasure.Potential
public import GibbsMeasure.Specification
public import GibbsMeasure.Mathlib.Logic.Function.DependsOn
public import GibbsMeasure.Mathlib.Topology.Algebra.InfiniteSum.Powerset
public import GibbsMeasure.Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

/-!
# Summable potentials

Hamiltonians of an interaction potential, Boltzmann factors, and absolute summability.
-/

@[expose] public section

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal

noncomputable section

namespace Potential

variable {S E : Type*} {Φ : Potential S E} {Λ Λ₁ Λ₂ : Finset S}

/-- Interaction terms entering the Hamiltonian in `Λ`, extended by zero. -/
def hamiltonianTerms (Φ : Potential S E) (Λ : Finset S) (η : S → E) : Finset S → ℝ :=
  {A | ¬ Disjoint A Λ}.indicator fun A ↦ Φ A η

@[simp] lemma hamiltonianTerms_of_not_disjoint (h : ¬ Disjoint Λ₁ Λ) (η : S → E) :
    Φ.hamiltonianTerms Λ η Λ₁ = Φ Λ₁ η := Set.indicator_of_mem h _

@[simp] lemma hamiltonianTerms_of_disjoint (h : Disjoint Λ₁ Λ) (η : S → E) :
    Φ.hamiltonianTerms Λ η Λ₁ = 0 := Set.indicator_of_notMem (by simpa using h) _

@[simp] lemma hamiltonianTerms_empty (Λ : Finset S) (η : S → E) :
    Φ.hamiltonianTerms Λ η ∅ = 0 :=
  hamiltonianTerms_of_disjoint (by simp) η

/-- Summability of the Hamiltonian series along `SummationFilter.powerset`. -/
class IsSummable (Φ : Potential S E) : Prop where
  summable (Λ : Finset S) (η : S → E) :
    Summable (Φ.hamiltonianTerms Λ η) (SummationFilter.powerset S)

/-- The Hamiltonian in volume `Λ`. -/
def hamiltonian (Φ : Potential S E) (Λ : Finset S) (η : S → E) : ℝ :=
  ∑'[SummationFilter.powerset S] A, Φ.hamiltonianTerms Λ η A

/-- The truncated Hamiltonian in volumes `Λ ⊆ Δ`. -/
def truncatedHamiltonian (Φ : Potential S E) (Λ Δ : Finset S) (η : S → E) : ℝ :=
  ∑ A ∈ Δ.powerset, Φ.hamiltonianTerms Λ η A

lemma hasSum_hamiltonian [IsSummable Φ] (Λ : Finset S) (η : S → E) :
    HasSum (Φ.hamiltonianTerms Λ η) (Φ.hamiltonian Λ η) (SummationFilter.powerset S) :=
  (IsSummable.summable Λ η).hasSum

lemma tendsto_truncatedHamiltonian [IsSummable Φ] (Λ : Finset S) (η : S → E) :
    Tendsto (Φ.truncatedHamiltonian Λ · η) atTop (nhds (Φ.hamiltonian Λ η)) :=
  HasSum.powerset_iff.1 (hasSum_hamiltonian (Φ := Φ) Λ η)

lemma IsSummable.of_summable (h : ∀ (Λ : Finset S) (η : S → E), Summable (Φ.hamiltonianTerms Λ η)) :
    IsSummable Φ where
  summable Λ η := (h Λ η).powerset

/-- Uniform convergence of the truncated Hamiltonians as `Δ ↑ S`. -/
class IsUniformlyConvergent (Φ : Potential S E) : Prop where
  tendstoUniformly (Λ : Finset S) :
    TendstoUniformly (fun Δ ↦ Φ.truncatedHamiltonian Λ Δ) (Φ.hamiltonian Λ) atTop

instance (priority := 80) IsUniformlyConvergent.isSummable [IsUniformlyConvergent Φ] :
    IsSummable Φ where
  summable Λ η := ⟨Φ.hamiltonian Λ η,
    HasSum.powerset_iff.2 ((IsUniformlyConvergent.tendstoUniformly (Φ := Φ) Λ).tendsto_at η)⟩

/-! ### The locally finitary case -/

lemma hamiltonianTerms_eq_zero_of_notMem_interactingSupport [IsFiniteRange Φ]
    (η : S → E) {A : Finset S} (hA : A ∉ interactingSupport (Φ := Φ) Λ) :
    Φ.hamiltonianTerms Λ η A = 0 := by
  by_cases h : Disjoint A Λ
  · simp [h]
  · simp [h, show Φ A = 0 from fun hΦ ↦ hA ((mem_interactingSupport (Φ := Φ)).2 ⟨h, hΦ⟩)]

@[simp] lemma hamiltonianTerms_eq_of_mem_interactingSupport [IsFiniteRange Φ]
    {A : Finset S} (hA : A ∈ interactingSupport (Φ := Φ) Λ) (η : S → E) :
    Φ.hamiltonianTerms Λ η A = Φ A η :=
  hamiltonianTerms_of_not_disjoint ((mem_interactingSupport (Φ := Φ)).1 hA).1 η

lemma hasSum_interactingHamiltonian [IsFiniteRange Φ] (Λ : Finset S) (η : S → E) :
    HasSum (Φ.hamiltonianTerms Λ η) (interactingHamiltonian (Φ := Φ) Λ η)
      (SummationFilter.powerset S) := by
  simpa [interactingHamiltonian] using
    (hasSum_sum_of_ne_finset_zero fun A hA ↦
      hamiltonianTerms_eq_zero_of_notMem_interactingSupport (Φ := Φ) η hA).powerset

instance (priority := 100) IsFiniteRange.isSummable [IsFiniteRange Φ] : IsSummable Φ where
  summable Λ η := ⟨_, hasSum_interactingHamiltonian (Φ := Φ) Λ η⟩

@[simp] lemma hamiltonian_eq_interactingHamiltonian [IsFiniteRange Φ]
    (Λ : Finset S) (η : S → E) :
    Φ.hamiltonian Λ η = interactingHamiltonian (Φ := Φ) Λ η :=
  (hasSum_interactingHamiltonian (Φ := Φ) Λ η).tsum_eq

lemma truncatedHamiltonian_eq_interactingHamiltonian [IsFiniteRange Φ]
    {Λ Δ : Finset S} (h : interactingSupport (Φ := Φ) Λ ⊆ Δ.powerset) (η : S → E) :
    Φ.truncatedHamiltonian Λ Δ η = interactingHamiltonian (Φ := Φ) Λ η := by
  rw [truncatedHamiltonian, ← Finset.sum_subset (f := Φ.hamiltonianTerms Λ η) h
    fun A _ hA' ↦ hamiltonianTerms_eq_zero_of_notMem_interactingSupport (Φ := Φ) η hA']
  simp [interactingHamiltonian]

lemma eventually_truncatedHamiltonian_eq_interactingHamiltonian [IsFiniteRange Φ]
    (Λ : Finset S) :
    ∀ᶠ Δ in atTop, Φ.truncatedHamiltonian Λ Δ = interactingHamiltonian (Φ := Φ) Λ := by
  classical
  filter_upwards [eventually_ge_atTop (interactingSupport (Φ := Φ) Λ).sup id] with Δ hΔ
  exact funext fun η ↦ truncatedHamiltonian_eq_interactingHamiltonian (Φ := Φ)
    (fun A hA ↦ Finset.mem_powerset.2 <| (Finset.le_sup (f := id) hA).trans hΔ) η

instance (priority := 100) IsFiniteRange.isUniformlyConvergent [IsFiniteRange Φ] :
    IsUniformlyConvergent Φ where
  tendstoUniformly Λ := by
    simpa using tendstoUniformly_of_eventually_eq
      (eventually_truncatedHamiltonian_eq_interactingHamiltonian (Φ := Φ) Λ)

/-! ### Hamiltonian differences -/

lemma hamiltonianTerms_sub (hΛ : Λ₁ ⊆ Λ₂) (η : S → E) :
    Φ.hamiltonianTerms Λ₂ η - Φ.hamiltonianTerms Λ₁ η
      = {A : Finset S | ¬ Disjoint A Λ₂ ∧ Disjoint A Λ₁}.indicator fun A ↦ Φ A η := by
  funext A
  by_cases h₁ : Disjoint A Λ₁ <;> by_cases h₂ : Disjoint A Λ₂
  · simp [h₁, h₂]
  · simp [h₁, h₂]
  · exact (h₁ <| h₂.mono_right hΛ).elim
  · simp [h₁, h₂]

lemma hasSum_hamiltonianTerms_sub [IsSummable Φ] (hΛ : Λ₁ ⊆ Λ₂) (η : S → E) :
    HasSum ({A : Finset S | ¬ Disjoint A Λ₂ ∧ Disjoint A Λ₁}.indicator fun A ↦ Φ A η)
      (Φ.hamiltonian Λ₂ η - Φ.hamiltonian Λ₁ η) (SummationFilter.powerset S) :=
  hamiltonianTerms_sub (Φ := Φ) hΛ η ▸
    (hasSum_hamiltonian (Φ := Φ) Λ₂ η).sub (hasSum_hamiltonian (Φ := Φ) Λ₁ η)

lemma hamiltonian_sub [IsSummable Φ] (hΛ : Λ₁ ⊆ Λ₂) (η : S → E) :
    Φ.hamiltonian Λ₂ η - Φ.hamiltonian Λ₁ η =
      ∑'[SummationFilter.powerset S] A,
        ({A : Finset S | ¬ Disjoint A Λ₂ ∧ Disjoint A Λ₁}.indicator fun A ↦ Φ A η) A :=
  (hasSum_hamiltonianTerms_sub (Φ := Φ) hΛ η).tsum_eq.symm

/-! ### Boltzmann factors -/

/-- Boltzmann factor `exp(-β H_Λ)`, valued in `ℝ≥0∞`. -/
def boltzmannFactor (Φ : Potential S E) (β : ℝ) (Λ : Finset S) (η : S → E) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-β * Φ.hamiltonian Λ η))

lemma boltzmannFactor_pos (β : ℝ) (Λ : Finset S) (η : S → E) : 0 < Φ.boltzmannFactor β Λ η := by
  simpa [boltzmannFactor] using Real.exp_pos (-β * Φ.hamiltonian Λ η)

lemma boltzmannFactor_ne_top (β : ℝ) (Λ : Finset S) (η : S → E) :
    Φ.boltzmannFactor β Λ η ≠ ⊤ := by simp [boltzmannFactor]

section MeasurableSpace

variable [MeasurableSpace E]

lemma dependsOn_of_disjoint [IsPotential Φ] {A : Finset S} (hA : Disjoint A Λ) :
    DependsOn (Φ A) ((Λ : Set S)ᶜ) :=
  ((IsPotential.measurable (Φ := Φ) A).dependsOn_of_cylinderEvents).mono fun x hx hxΛ ↦
    (Finset.disjoint_left.1 hA (by simpa using hx)) (by simpa using hxΛ)

lemma dependsOn_sum_hamiltonianTerms_sub [IsPotential Φ] (Λ₁ Λ₂ : Finset S)
    (s : Finset (Finset S)) :
    DependsOn (fun η ↦ ∑ A ∈ s,
      ({A : Finset S | ¬ Disjoint A Λ₂ ∧ Disjoint A Λ₁}.indicator fun A ↦ Φ A η) A)
      ((Λ₁ : Set S)ᶜ) := by
  refine DependsOn.sum fun A _ ↦ ?_
  by_cases hA : ¬ Disjoint A Λ₂ ∧ Disjoint A Λ₁
  · simpa [Set.indicator_of_mem hA] using dependsOn_of_disjoint (Φ := Φ) hA.2
  · simpa [Set.indicator_of_notMem hA] using dependsOn_of_const (0 : ℝ)

theorem dependsOn_hamiltonian_sub [IsPotential Φ] [IsSummable Φ] (hΛ : Λ₁ ⊆ Λ₂) :
    DependsOn (fun η ↦ Φ.hamiltonian Λ₂ η - Φ.hamiltonian Λ₁ η) ((Λ₁ : Set S)ᶜ) :=
  DependsOn.of_tendsto (l := (SummationFilter.powerset S).filter)
    (F := fun s η ↦ ∑ A ∈ s,
      ({A : Finset S | ¬ Disjoint A Λ₂ ∧ Disjoint A Λ₁}.indicator fun A ↦ Φ A η) A)
    (fun s ↦ dependsOn_sum_hamiltonianTerms_sub (Φ := Φ) Λ₁ Λ₂ s)
    fun η ↦ hasSum_hamiltonianTerms_sub (Φ := Φ) hΛ η

theorem hamiltonian_sub_eq_of_subset_eqOn_compl [IsPotential Φ] [IsSummable Φ] {η ζ : S → E}
    (hΛ : Λ₁ ⊆ Λ₂) (hrestrict : ∀ s ∉ Λ₁, ζ s = η s) :
    Φ.hamiltonian Λ₁ η - Φ.hamiltonian Λ₁ ζ = Φ.hamiltonian Λ₂ η - Φ.hamiltonian Λ₂ ζ := by
  simpa [sub_eq_sub_iff_add_eq_add, add_comm] using
    dependsOn_hamiltonian_sub (Φ := Φ) hΛ (x := ζ) (y := η)
      fun i hi ↦ hrestrict i (by simpa using hi)

lemma measurable_sum_hamiltonianTerms [IsPotential Φ] (Λ : Finset S) (s : Finset (Finset S)) :
    Measurable fun η : S → E ↦ ∑ A ∈ s, Φ.hamiltonianTerms Λ η A := by
  refine Finset.measurable_sum _ fun A _ ↦ ?_
  by_cases hA : Disjoint A Λ
  · simp [hA]
  · simpa [hA] using
      (IsPotential.measurable (Φ := Φ) A).mono cylinderEvents_le_pi le_rfl

@[fun_prop]
lemma measurable_hamiltonian [Countable S] [IsPotential Φ] [IsSummable Φ] (Λ : Finset S) :
    Measurable (Φ.hamiltonian Λ) :=
  measurable_of_tendsto_metrizable' (SummationFilter.powerset S).filter
    (fun s ↦ measurable_sum_hamiltonianTerms (Φ := Φ) Λ s)
    (tendsto_pi_nhds.2 fun η ↦ hasSum_hamiltonian (Φ := Φ) Λ η)

@[fun_prop]
lemma measurable_hamiltonian_of_isFiniteRange [IsPotential Φ] [IsFiniteRange Φ] (Λ : Finset S) :
    Measurable (Φ.hamiltonian Λ) := by
  simpa using measurable_interactingHamiltonian (Φ := Φ) Λ

lemma measurable_hamiltonian_sub_of_measurable [IsPotential Φ] [IsSummable Φ]
    (hmeas : ∀ Λ, Measurable (Φ.hamiltonian Λ)) (hΛ : Λ₁ ⊆ Λ₂) :
    Measurable[cylinderEvents (Λ₁ : Set S)ᶜ]
      (fun η ↦ Φ.hamiltonian Λ₂ η - Φ.hamiltonian Λ₁ η) :=
  ((hmeas Λ₂).sub (hmeas Λ₁)).cylinderEvents_of_dependsOn
    (dependsOn_hamiltonian_sub (Φ := Φ) hΛ)

lemma measurable_hamiltonian_sub [Countable S] [IsPotential Φ] [IsSummable Φ] (hΛ : Λ₁ ⊆ Λ₂) :
    Measurable[cylinderEvents (Λ₁ : Set S)ᶜ]
      (fun η ↦ Φ.hamiltonian Λ₂ η - Φ.hamiltonian Λ₁ η) :=
  measurable_hamiltonian_sub_of_measurable (measurable_hamiltonian (Φ := Φ)) hΛ

lemma measurable_boltzmannFactor_of_measurable (h : ∀ Λ, Measurable (Φ.hamiltonian Λ))
    (β : ℝ) (Λ : Finset S) : Measurable (Φ.boltzmannFactor β Λ) :=
  ((measurable_const.mul (h Λ)).exp).ennreal_ofReal

@[fun_prop]
lemma measurable_boltzmannFactor [Countable S] [IsPotential Φ] [IsSummable Φ]
    (β : ℝ) (Λ : Finset S) : Measurable (Φ.boltzmannFactor β Λ) :=
  measurable_boltzmannFactor_of_measurable (measurable_hamiltonian (Φ := Φ)) β Λ

theorem isPremodifier_boltzmannFactor_of_measurable [IsPotential Φ] [IsSummable Φ]
    (hmeas : ∀ Λ, Measurable (Φ.hamiltonian Λ)) (β : ℝ) :
    Specification.IsPremodifier (S := S) (E := E) (Φ.boltzmannFactor β) where
  measurable Λ := measurable_boltzmannFactor_of_measurable hmeas β Λ
  comm_of_subset {Λ₁ Λ₂ ζ η} hΛ hrestrict := by
    simp only [boltzmannFactor]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← ENNReal.ofReal_mul (Real.exp_nonneg _),
      ← Real.exp_add, ← Real.exp_add]
    simp [← mul_add]
    congr 3
    linarith [hamiltonian_sub_eq_of_subset_eqOn_compl (Φ := Φ) hΛ hrestrict]

theorem isPremodifier_boltzmannFactor [Countable S] [IsPotential Φ] [IsSummable Φ] (β : ℝ) :
    Specification.IsPremodifier (S := S) (E := E) (Φ.boltzmannFactor β) :=
  isPremodifier_boltzmannFactor_of_measurable (measurable_hamiltonian (Φ := Φ)) β

theorem isPremodifier_boltzmannFactor_of_isFiniteRange [IsPotential Φ] [IsFiniteRange Φ] (β : ℝ) :
    Specification.IsPremodifier (S := S) (E := E) (Φ.boltzmannFactor β) :=
  isPremodifier_boltzmannFactor_of_measurable
    (measurable_hamiltonian_of_isFiniteRange (Φ := Φ)) β

end MeasurableSpace

/-! ### Absolutely summable potentials -/

/-- `‖Φ‖ᵢ`, the total sup-norm of the interaction terms containing `i`. -/
def normAt (Φ : Potential S E) (i : S) : ℝ≥0∞ :=
  ∑' A : Finset S, {A : Finset S | i ∈ A}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) A

/-- `Φ` is absolutely summable. -/
class IsAbsolutelySummable (Φ : Potential S E) : Prop where
  normAt_ne_top (i : S) : Φ.normAt i ≠ ⊤

variable (Φ) in
/-- The sup-norms of the interaction terms entering `H_Λ`, extended by zero. -/
def termNorm (Λ : Finset S) : Finset S → ℝ≥0∞ :=
  {A : Finset S | ¬ Disjoint A Λ}.indicator fun A ↦ ⨆ η, ‖Φ A η‖ₑ

@[simp] lemma termNorm_of_not_disjoint {A : Finset S} (h : ¬ Disjoint A Λ) :
    Φ.termNorm Λ A = ⨆ η, ‖Φ A η‖ₑ :=
  Set.indicator_of_mem h _

@[simp] lemma termNorm_of_disjoint {A : Finset S} (h : Disjoint A Λ) :
    Φ.termNorm Λ A = 0 :=
  Set.indicator_of_notMem (by simpa using h) _

lemma enorm_hamiltonianTerms_le_termNorm (Λ : Finset S) (η : S → E) (A : Finset S) :
    ‖Φ.hamiltonianTerms Λ η A‖ₑ ≤ Φ.termNorm Λ A := by
  by_cases h : Disjoint A Λ <;> simp [h, le_iSup]

lemma termNorm_le_sum (Λ : Finset S) (A : Finset S) :
    Φ.termNorm Λ A ≤ ∑ i ∈ Λ, {A : Finset S | i ∈ A}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) A := by
  by_cases h : Disjoint A Λ
  · simp [h]
  · obtain ⟨i, hiA, hiΛ⟩ := Finset.not_disjoint_iff.1 h
    simpa [h, Set.indicator_of_mem (show A ∈ {B | i ∈ B} from hiA)] using
      Finset.single_le_sum (f := fun i ↦
        {A : Finset S | i ∈ A}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) A) (fun _ _ ↦ bot_le) hiΛ

lemma tsum_termNorm_le (Λ : Finset S) : ∑' A : Finset S, Φ.termNorm Λ A ≤ ∑ i ∈ Λ, Φ.normAt i :=
  (ENNReal.tsum_le_tsum (termNorm_le_sum (Φ := Φ) Λ)).trans <| by
    simpa [Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable, normAt]

lemma sum_normAt_ne_top [IsAbsolutelySummable Φ] (Λ : Finset S) :
    (∑ i ∈ Λ, Φ.normAt i) ≠ ⊤ :=
  (ENNReal.sum_lt_top.2 fun _ _ ↦ (IsAbsolutelySummable.normAt_ne_top (Φ := Φ) _).lt_top).ne

lemma tsum_termNorm_ne_top [IsAbsolutelySummable Φ] (Λ : Finset S) :
    ∑' A : Finset S, Φ.termNorm Λ A ≠ ⊤ :=
  ne_top_of_le_ne_top (sum_normAt_ne_top (Φ := Φ) Λ) (tsum_termNorm_le (Φ := Φ) Λ)

lemma termNorm_ne_top [IsAbsolutelySummable Φ] (Λ A : Finset S) : Φ.termNorm Λ A ≠ ⊤ :=
  ENNReal.ne_top_of_tsum_ne_top (tsum_termNorm_ne_top (Φ := Φ) Λ) A

lemma abs_hamiltonianTerms_le_termNorm_toReal [IsAbsolutelySummable Φ]
    (Λ : Finset S) (η : S → E) (A : Finset S) :
    ‖Φ.hamiltonianTerms Λ η A‖ ≤ (Φ.termNorm Λ A).toReal := by
  simpa [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (norm_nonneg _)] using
    ENNReal.toReal_mono (termNorm_ne_top (Φ := Φ) Λ A)
      (enorm_hamiltonianTerms_le_termNorm (Φ := Φ) Λ η A)

lemma tsum_enorm_hamiltonianTerms_le (Λ : Finset S) (η : S → E) :
    ∑' A : Finset S, ‖Φ.hamiltonianTerms Λ η A‖ₑ ≤ ∑ i ∈ Λ, Φ.normAt i :=
  (ENNReal.tsum_le_tsum (enorm_hamiltonianTerms_le_termNorm (Φ := Φ) Λ η)).trans
    (tsum_termNorm_le (Φ := Φ) Λ)

lemma summable_hamiltonianTerms [IsAbsolutelySummable Φ] (Λ : Finset S) (η : S → E) :
    Summable (Φ.hamiltonianTerms Λ η) :=
  Summable.of_enorm <| ne_top_of_le_ne_top (sum_normAt_ne_top (Φ := Φ) Λ)
    (tsum_enorm_hamiltonianTerms_le Λ η)

instance (priority := 100) IsAbsolutelySummable.isSummable [IsAbsolutelySummable Φ] :
    IsSummable Φ where
  summable Λ η := (summable_hamiltonianTerms (Φ := Φ) Λ η).powerset

lemma hamiltonian_eq_tsum [IsAbsolutelySummable Φ] (Λ : Finset S) (η : S → E) :
    Φ.hamiltonian Λ η = ∑' A : Finset S, Φ.hamiltonianTerms Λ η A :=
  ((summable_hamiltonianTerms (Φ := Φ) Λ η).hasSum.powerset).tsum_eq

lemma tendstoUniformly_sum_hamiltonianTerms [IsAbsolutelySummable Φ] (Λ : Finset S) :
    TendstoUniformly (fun s : Finset (Finset S) ↦ fun η ↦ ∑ A ∈ s, Φ.hamiltonianTerms Λ η A)
      (Φ.hamiltonian Λ) atTop := by
  rw [← tendstoUniformlyOn_univ]
  exact (tendstoUniformlyOn_univ.1 <| tendstoUniformly_tsum
      (ENNReal.summable_toReal (tsum_termNorm_ne_top (Φ := Φ) Λ))
      fun A η ↦ abs_hamiltonianTerms_le_termNorm_toReal (Φ := Φ) Λ η A).congr_right
    fun η _ ↦ (hamiltonian_eq_tsum (Φ := Φ) Λ η).symm

lemma hasSumUniformly_hamiltonianTerms [IsAbsolutelySummable Φ] (Λ : Finset S) :
    HasSumUniformly (fun A η ↦ Φ.hamiltonianTerms Λ η A) (Φ.hamiltonian Λ) :=
  hasSumUniformly_iff_tendstoUniformly.2 (tendstoUniformly_sum_hamiltonianTerms (Φ := Φ) Λ)

instance (priority := 100) IsAbsolutelySummable.isUniformlyConvergent [IsAbsolutelySummable Φ] :
    IsUniformlyConvergent Φ where
  tendstoUniformly Λ :=
    (tendstoUniformly_sum_hamiltonianTerms (Φ := Φ) Λ).comp_tendsto
      Filter.tendsto_finset_powerset_atTop_atTop

theorem enorm_hamiltonian_le [IsAbsolutelySummable Φ] (Λ : Finset S) (η : S → E) :
    ‖Φ.hamiltonian Λ η‖ₑ ≤ ∑ i ∈ Λ, Φ.normAt i := by
  rw [hamiltonian_eq_tsum (Φ := Φ) Λ η]
  exact enorm_tsum_le_tsum_enorm.trans (tsum_enorm_hamiltonianTerms_le Λ η)

theorem iSup_enorm_hamiltonian_le [IsAbsolutelySummable Φ] (Λ : Finset S) :
    ⨆ η, ‖Φ.hamiltonian Λ η‖ₑ ≤ ∑ i ∈ Λ, Φ.normAt i :=
  iSup_le fun η ↦ enorm_hamiltonian_le (Φ := Φ) Λ η

lemma abs_hamiltonian_le [IsAbsolutelySummable Φ] (Λ : Finset S) (η : S → E) :
    |Φ.hamiltonian Λ η| ≤ (∑ i ∈ Λ, Φ.normAt i).toReal := by
  simpa [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)] using
    ENNReal.toReal_mono (sum_normAt_ne_top (Φ := Φ) Λ) (enorm_hamiltonian_le (Φ := Φ) Λ η)

/-- Absolute summability bounds every interaction term on a nonempty support. -/
lemma IsAbsolutelySummable.iSup_enorm_ne_top [IsAbsolutelySummable Φ] {A : Finset S}
    (hA : A.Nonempty) : ⨆ η, ‖Φ A η‖ₑ ≠ ⊤ := by
  obtain ⟨i, hi⟩ := hA
  simpa [Set.indicator_of_mem (show A ∈ {B : Finset S | i ∈ B} from hi)] using
    ENNReal.ne_top_of_tsum_ne_top (IsAbsolutelySummable.normAt_ne_top (Φ := Φ) i) A

lemma IsFiniteRange.normAt_eq_sum [IsFiniteRange Φ] (i : S) {Δ : Finset S}
    (hΔ : ∀ A : Finset S, i ∈ A → Φ A ≠ 0 → A ⊆ Δ) :
    Φ.normAt i =
      ∑ A ∈ Δ.powerset, {A : Finset S | i ∈ A}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) A := by
  refine tsum_eq_sum fun A hA ↦ ?_
  by_cases hi : i ∈ A
  · by_cases hΦ : Φ A = 0
    · simp [hi, hΦ]
    · exact (hA (Finset.mem_powerset.2 (hΔ A hi hΦ))).elim
  · simp [hi]

lemma IsFiniteRange.isAbsolutelySummable [IsFiniteRange Φ]
    (h : ∀ A : Finset S, A.Nonempty → ⨆ η, ‖Φ A η‖ₑ ≠ ⊤) : IsAbsolutelySummable Φ where
  normAt_ne_top i := by
    obtain ⟨Δ, hΔ⟩ := IsFiniteRange.exists_finset (Φ := Φ) i
    rw [IsFiniteRange.normAt_eq_sum (Φ := Φ) i hΔ]
    refine (ENNReal.sum_lt_top.2 fun A _ ↦ ?_).ne
    by_cases hi : i ∈ A
    · simpa [hi] using (h A ⟨i, hi⟩).lt_top
    · simp [hi]

lemma IsFiniteRange.isAbsolutelySummable_iff [IsFiniteRange Φ] :
    IsAbsolutelySummable Φ ↔ ∀ A : Finset S, A.Nonempty → ⨆ η, ‖Φ A η‖ₑ ≠ ⊤ :=
  ⟨fun _ _ hA ↦ IsAbsolutelySummable.iSup_enorm_ne_top hA,
    IsFiniteRange.isAbsolutelySummable⟩

/-! ### Truncation and density in the interaction seminorms -/

lemma iSup_enorm_truncation_le (Δ B : Finset S) :
    ⨆ η, ‖Φ.truncation Δ B η‖ₑ ≤ ⨆ η, ‖Φ B η‖ₑ := by
  classical
  exact iSup_le fun η ↦ by by_cases h : B ⊆ Δ <;> simp [h, le_iSup]

lemma normAt_truncation_le (Δ : Finset S) (i : S) :
    (Φ.truncation Δ).normAt i ≤ Φ.normAt i :=
  ENNReal.tsum_le_tsum fun B ↦ by
    by_cases hi : i ∈ B <;> simp [hi, iSup_enorm_truncation_le]

instance (Δ : Finset S) [IsAbsolutelySummable Φ] : IsAbsolutelySummable (Φ.truncation Δ) where
  normAt_ne_top i := ne_top_of_le_ne_top (IsAbsolutelySummable.normAt_ne_top (Φ := Φ) i)
    (normAt_truncation_le Δ i)

variable (Φ) in
/-- The tail `∑_{A ∩ Λ ≠ ∅, A ⊄ Δ} ‖Φ_A‖` of the interaction series in the volume `Λ`. -/
def tailWeight (Δ Λ : Finset S) : ℝ≥0∞ :=
  ∑' A : Finset S,
    {A : Finset S | ¬ Disjoint A Λ ∧ ¬ A ⊆ Δ}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) A

lemma tailWeight_le_tsum_termNorm (Δ Λ : Finset S) :
    Φ.tailWeight Δ Λ ≤ ∑' A : Finset S, Φ.termNorm Λ A :=
  ENNReal.tsum_le_tsum fun B ↦ by
    by_cases hB : B ∈ {A : Finset S | ¬ Disjoint A Λ ∧ ¬ A ⊆ Δ}
    · rw [Set.indicator_of_mem hB, termNorm_of_not_disjoint hB.1]
    · simp [hB]

lemma tailWeight_ne_top [IsAbsolutelySummable Φ] (Δ Λ : Finset S) :
    Φ.tailWeight Δ Λ ≠ ⊤ :=
  ne_top_of_le_ne_top (tsum_termNorm_ne_top (Φ := Φ) Λ) (tailWeight_le_tsum_termNorm Δ Λ)

lemma indicator_tail_eq (Δ Λ B : Finset S) :
    {A : Finset S | ¬ Disjoint A Λ ∧ ¬ A ⊆ Δ}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) B
      = {A : Finset S | A ∉ Δ.powerset}.indicator (Φ.termNorm Λ) B := by
  classical
  by_cases hsub : B ⊆ Δ <;> by_cases hd : Disjoint B Λ <;>
    simp [termNorm, hsub, hd, Finset.mem_powerset]

lemma tailWeight_eq_tsum_compl (Δ Λ : Finset S) :
    Φ.tailWeight Δ Λ
      = ∑' B : {A : Finset S // A ∉ Δ.powerset}, Φ.termNorm Λ (B : Finset S) :=
  (tsum_congr fun B ↦ indicator_tail_eq Δ Λ B).trans
    (tsum_subtype {A : Finset S | A ∉ Δ.powerset} (Φ.termNorm Λ)).symm

theorem tendsto_tailWeight_atTop [IsAbsolutelySummable Φ] (Λ : Finset S) :
    Tendsto (fun Δ : Finset S ↦ Φ.tailWeight Δ Λ) atTop (𝓝 0) := by
  simpa [tailWeight_eq_tsum_compl, Function.comp_def] using
    (ENNReal.tendsto_tsum_compl_atTop_zero (tsum_termNorm_ne_top (Φ := Φ) Λ)).comp
      tendsto_finset_powerset_atTop_atTop

lemma normAt_sub_truncation (Δ : Finset S) (i : S) :
    (Φ - Φ.truncation Δ).normAt i = Φ.tailWeight Δ {i} := by
  classical
  refine tsum_congr fun A ↦ ?_
  by_cases hi : i ∈ A <;> by_cases hAΔ : A ⊆ Δ <;>
    simp [hi, hAΔ, Finset.disjoint_singleton_right]

theorem tendsto_normAt_sub_truncation [IsAbsolutelySummable Φ] (i : S) :
    Tendsto (fun Δ : Finset S ↦ (Φ - Φ.truncation Δ).normAt i) atTop (𝓝 0) := by
  simpa [normAt_sub_truncation] using tendsto_tailWeight_atTop (Φ := Φ) {i}

end Potential
