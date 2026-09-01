/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
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
# Potentials and their Hamiltonians

An interaction potential (`Potential.IsPotential`) is summable when the Hamiltonian series
`H_Λ = ∑_{A ∩ Λ ≠ ∅} Φ_A` converges along `SummationFilter.powerset` (`Potential.IsSummable`).
Uniform convergence of the truncated Hamiltonians is `Potential.IsUniformlyConvergent`. Finite
range is the special case in which the series has finite support.

## Main results

* `Potential.hamiltonian_sub`: the Hamiltonian difference as a series, and
  `Potential.dependsOn_hamiltonian_sub` / `Potential.measurable_hamiltonian_sub`.
* `Potential.isPremodifier_boltzmannFactor`: Boltzmann factors form a pre-modification.
  Countability of `S` is used only for measurability of the infinite Hamiltonian;
  `isPremodifier_boltzmannFactor_of_measurable` and
  `isPremodifier_boltzmannFactor_of_isFiniteRange` drop it.
* `Potential.IsAbsolutelySummable`: absolute summability, with `‖Φ‖ᵢ` as `Potential.normAt`; it
  implies uniform convergence of the truncated Hamiltonians, hence `IsSummable`, and bounds the
  Hamiltonian. Finite range potentials are absolutely summable iff every term on a nonempty
  support is bounded (`IsFiniteRange.isAbsolutelySummable_iff`).
* `Potential.tendsto_normAt_sub_truncation`: the truncations `Φ^Δ` approximate `Φ` in each
  interaction seminorm.
-/

@[expose] public section

open Filter Function MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal

noncomputable section

namespace Potential

variable {S E : Type*} {Φ : Potential S E} {Λ Λ₁ Λ₂ : Finset S}

/-- The interaction terms entering the Hamiltonian in `Λ`, extended by zero. -/
def hamiltonianTerms (Φ : Potential S E) (Λ : Finset S) (η : S → E) : Finset S → ℝ :=
  {A | ¬ Disjoint A Λ}.indicator fun A ↦ Φ A η

lemma hamiltonianTerms_of_not_disjoint (h : ¬ Disjoint Λ₁ Λ) (η : S → E) :
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
  SummationFilter.hasSum_powerset_iff.1 (hasSum_hamiltonian (Φ := Φ) Λ η)

/-- Unconditional summability of the interaction terms suffices. -/
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
    SummationFilter.hasSum_powerset_iff.2
      ((IsUniformlyConvergent.tendstoUniformly (Φ := Φ) Λ).tendsto_at η)⟩

/-! ### The locally finitary case -/

lemma hamiltonianTerms_eq_zero_of_notMem_interactingSupport [IsFiniteRange Φ]
    (η : S → E) {A : Finset S} (hA : A ∉ interactingSupport (Φ := Φ) Λ) :
    Φ.hamiltonianTerms Λ η A = 0 := by
  by_cases hdisj : Disjoint A Λ
  · exact hamiltonianTerms_of_disjoint hdisj η
  · obtain ⟨x, hxA, hxΛ⟩ := Finset.not_disjoint_iff.1 hdisj
    have hne : ((A : Set S) ∩ (Λ : Set S)).Nonempty := ⟨x, by simpa using hxA, by simpa using hxΛ⟩
    have : Φ A = 0 := by
      by_contra hΦ
      exact hA ((mem_interactingSupport (Φ := Φ)).2 ⟨hne, hΦ⟩)
    simp [hamiltonianTerms, this]

lemma hasSum_interactingHamiltonian [IsFiniteRange Φ] (Λ : Finset S) (η : S → E) :
    HasSum (Φ.hamiltonianTerms Λ η) (interactingHamiltonian (Φ := Φ) Λ η)
      (SummationFilter.powerset S) := by
  have h : HasSum (Φ.hamiltonianTerms Λ η)
      (∑ A ∈ interactingSupport (Φ := Φ) Λ, Φ.hamiltonianTerms Λ η A) :=
    hasSum_sum_of_ne_finset_zero fun A hA ↦
      hamiltonianTerms_eq_zero_of_notMem_interactingSupport (Φ := Φ) η hA
  have hsum : (∑ A ∈ interactingSupport (Φ := Φ) Λ, Φ.hamiltonianTerms Λ η A)
      = interactingHamiltonian (Φ := Φ) Λ η := by
    refine Finset.sum_congr rfl fun A hA ↦ ?_
    obtain ⟨⟨x, hxA, hxΛ⟩, -⟩ := (mem_interactingSupport (Φ := Φ)).1 hA
    exact hamiltonianTerms_of_not_disjoint
      (Finset.not_disjoint_iff.2 ⟨x, by simpa using hxA, by simpa using hxΛ⟩) η
  exact hsum ▸ h.powerset

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
  refine Finset.sum_congr rfl fun A hA ↦ ?_
  obtain ⟨⟨x, hxA, hxΛ⟩, -⟩ := (mem_interactingSupport (Φ := Φ)).1 hA
  exact hamiltonianTerms_of_not_disjoint
    (Finset.not_disjoint_iff.2 ⟨x, by simpa using hxA, by simpa using hxΛ⟩) η

lemma eventually_truncatedHamiltonian_eq_interactingHamiltonian [IsFiniteRange Φ]
    (Λ : Finset S) :
    ∀ᶠ Δ in atTop, Φ.truncatedHamiltonian Λ Δ = interactingHamiltonian (Φ := Φ) Λ := by
  classical
  refine Filter.eventually_atTop.2 ⟨(interactingSupport (Φ := Φ) Λ).sup id, fun Δ hΔ ↦ ?_⟩
  funext η
  refine truncatedHamiltonian_eq_interactingHamiltonian (Φ := Φ) ?_ η
  intro A hA
  exact Finset.mem_powerset.2 <| (Finset.le_sup (f := id) hA).trans hΔ

instance (priority := 100) IsFiniteRange.isUniformlyConvergent [IsFiniteRange Φ] :
    IsUniformlyConvergent Φ where
  tendstoUniformly Λ := by
    have hH : Φ.hamiltonian Λ = interactingHamiltonian (Φ := Φ) Λ :=
      funext fun η ↦ hamiltonian_eq_interactingHamiltonian (Φ := Φ) Λ η
    rw [hH]
    exact tendstoUniformly_of_eventually_eq
      (eventually_truncatedHamiltonian_eq_interactingHamiltonian (Φ := Φ) Λ)

/-! ### Hamiltonian differences -/

/-- The terms of `H_Λ₂ - H_Λ₁`, for `Λ₁ ⊆ Λ₂`. -/
lemma hamiltonianTerms_sub (hΛ : Λ₁ ⊆ Λ₂) (η : S → E) :
    Φ.hamiltonianTerms Λ₂ η - Φ.hamiltonianTerms Λ₁ η
      = {A : Finset S | ¬ Disjoint A Λ₂ ∧ Disjoint A Λ₁}.indicator fun A ↦ Φ A η := by
  funext A
  by_cases h₁ : Disjoint A Λ₁
  · by_cases h₂ : Disjoint A Λ₂
    · simp [hamiltonianTerms, Set.indicator_of_notMem, h₁, h₂]
    · rw [Pi.sub_apply, hamiltonianTerms_of_not_disjoint h₂, hamiltonianTerms_of_disjoint h₁,
        Set.indicator_of_mem (show A ∈ {A : Finset S | ¬ Disjoint A Λ₂ ∧ Disjoint A Λ₁} from
          ⟨h₂, h₁⟩), sub_zero]
  · have h₂ : ¬ Disjoint A Λ₂ := fun h ↦ h₁ (h.mono_right hΛ)
    rw [Pi.sub_apply, hamiltonianTerms_of_not_disjoint h₂, hamiltonianTerms_of_not_disjoint h₁,
      Set.indicator_of_notMem (show A ∉ {A : Finset S | ¬ Disjoint A Λ₂ ∧ Disjoint A Λ₁} from
        fun h ↦ h₁ h.2), sub_self]

lemma hasSum_hamiltonianTerms_sub [IsSummable Φ] (hΛ : Λ₁ ⊆ Λ₂) (η : S → E) :
    HasSum ({A : Finset S | ¬ Disjoint A Λ₂ ∧ Disjoint A Λ₁}.indicator fun A ↦ Φ A η)
      (Φ.hamiltonian Λ₂ η - Φ.hamiltonian Λ₁ η) (SummationFilter.powerset S) :=
  hamiltonianTerms_sub (Φ := Φ) hΛ η ▸
    (hasSum_hamiltonian (Φ := Φ) Λ₂ η).sub (hasSum_hamiltonian (Φ := Φ) Λ₁ η)

/-- For `Λ₁ ⊆ Λ₂`,
`H_Λ₂ - H_Λ₁ = ∑_{A ∩ Λ₂ ≠ ∅, A ∩ Λ₁ = ∅} Φ_A`. -/
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

/-- An interaction term disjoint from `Λ` depends only on the coordinates outside `Λ`. -/
lemma dependsOn_of_disjoint [IsPotential Φ] {A : Finset S} (hA : Disjoint A Λ) :
    DependsOn (Φ A) ((Λ : Set S)ᶜ) :=
  ((IsPotential.measurable (Φ := Φ) A).dependsOn_of_cylinderEvents).mono fun x hx hxΛ ↦
    (Finset.disjoint_left.1 hA (by simpa using hx)) (by simpa using hxΛ)

lemma dependsOn_sum_hamiltonianTerms_sub [IsPotential Φ] (Λ₁ Λ₂ : Finset S)
    (s : Finset (Finset S)) :
    DependsOn (fun η ↦ ∑ A ∈ s,
      ({A : Finset S | ¬ Disjoint A Λ₂ ∧ Disjoint A Λ₁}.indicator fun A ↦ Φ A η) A)
      ((Λ₁ : Set S)ᶜ) := by
  refine DependsOn.sum fun A _ x y hxy ↦ ?_
  by_cases hA : ¬ Disjoint A Λ₂ ∧ Disjoint A Λ₁
  · have hmem : A ∈ {B : Finset S | ¬ Disjoint B Λ₂ ∧ Disjoint B Λ₁} := hA
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
    exact dependsOn_of_disjoint (Φ := Φ) hA.2 hxy
  · have hmem : A ∉ {B : Finset S | ¬ Disjoint B Λ₂ ∧ Disjoint B Λ₁} := hA
    rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]

/-- For `Λ₁ ⊆ Λ₂` the Hamiltonian difference depends only on the coordinates outside `Λ₁`. -/
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
  have h := dependsOn_hamiltonian_sub (Φ := Φ) hΛ (x := ζ) (y := η)
    fun i hi ↦ hrestrict i (by simpa using hi)
  rw [sub_eq_sub_iff_add_eq_add] at h ⊢
  simpa [add_comm] using h

lemma measurable_sum_hamiltonianTerms [IsPotential Φ] (Λ : Finset S) (s : Finset (Finset S)) :
    Measurable fun η : S → E ↦ ∑ A ∈ s, Φ.hamiltonianTerms Λ η A := by
  refine Finset.measurable_sum _ fun A _ ↦ ?_
  by_cases hA : Disjoint A Λ
  · simpa only [hamiltonianTerms_of_disjoint hA] using measurable_const (a := (0 : ℝ))
  · simpa only [hamiltonianTerms_of_not_disjoint hA] using
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
  have : Φ.hamiltonian Λ = interactingHamiltonian (Φ := Φ) Λ :=
    funext fun η ↦ hamiltonian_eq_interactingHamiltonian (Φ := Φ) Λ η
  rw [this]
  exact measurable_interactingHamiltonian (Φ := Φ) Λ

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

private lemma ofReal_exp_add (a b : ℝ) :
    ENNReal.ofReal (Real.exp (a + b)) =
      ENNReal.ofReal (Real.exp a) * ENNReal.ofReal (Real.exp b) := by
  rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg a)]

/-- The Boltzmann factors of a potential form a pre-modification, given measurability of the
Hamiltonian. Countability of `S` is not required for the exchange identity. -/
theorem isPremodifier_boltzmannFactor_of_measurable [IsPotential Φ] [IsSummable Φ]
    (hmeas : ∀ Λ, Measurable (Φ.hamiltonian Λ)) (β : ℝ) :
    Specification.IsPremodifier (S := S) (E := E) (Φ.boltzmannFactor β) where
  measurable Λ := measurable_boltzmannFactor_of_measurable hmeas β Λ
  comm_of_subset {Λ₁ Λ₂ ζ η} hΛ hrestrict := by
    have hH := hamiltonian_sub_eq_of_subset_eqOn_compl (Φ := Φ) hΛ hrestrict
    rw [boltzmannFactor, boltzmannFactor, boltzmannFactor, boltzmannFactor,
      ← ofReal_exp_add, ← ofReal_exp_add]
    refine congrArg (ENNReal.ofReal ∘ Real.exp) ?_
    simp only [← mul_add]
    refine congrArg (fun x ↦ -β * x) ?_
    rw [sub_eq_sub_iff_add_eq_add] at hH
    simpa [add_comm] using hH

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

lemma termNorm_of_not_disjoint {A : Finset S} (h : ¬ Disjoint A Λ) :
    Φ.termNorm Λ A = ⨆ η, ‖Φ A η‖ₑ :=
  Set.indicator_of_mem h _

lemma termNorm_of_disjoint {A : Finset S} (h : Disjoint A Λ) :
    Φ.termNorm Λ A = 0 :=
  Set.indicator_of_notMem (by simpa using h) _

lemma enorm_hamiltonianTerms_le_termNorm (Λ : Finset S) (η : S → E) (A : Finset S) :
    ‖Φ.hamiltonianTerms Λ η A‖ₑ ≤ Φ.termNorm Λ A := by
  by_cases h : Disjoint A Λ
  · simp [hamiltonianTerms_of_disjoint h, termNorm_of_disjoint h]
  · rw [hamiltonianTerms_of_not_disjoint h, termNorm_of_not_disjoint h]
    exact le_iSup (fun η ↦ ‖Φ A η‖ₑ) η

lemma termNorm_le_sum (Λ : Finset S) (A : Finset S) :
    Φ.termNorm Λ A ≤ ∑ i ∈ Λ, {A : Finset S | i ∈ A}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) A := by
  by_cases h : Disjoint A Λ
  · simp [termNorm_of_disjoint h]
  · obtain ⟨i, hiA, hiΛ⟩ := Finset.not_disjoint_iff.1 h
    refine le_trans ?_ (Finset.single_le_sum (f := fun i ↦
      {A : Finset S | i ∈ A}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) A) (fun _ _ ↦ bot_le) hiΛ)
    rw [termNorm_of_not_disjoint h,
      Set.indicator_of_mem (show A ∈ {B : Finset S | i ∈ B} from hiA)]

lemma tsum_termNorm_le (Λ : Finset S) : ∑' A : Finset S, Φ.termNorm Λ A ≤ ∑ i ∈ Λ, Φ.normAt i := by
  refine le_trans (ENNReal.tsum_le_tsum (termNorm_le_sum (Φ := Φ) Λ)) ?_
  rw [Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable]
  exact le_of_eq (Finset.sum_congr rfl fun i _ ↦ rfl)

lemma sum_normAt_ne_top [IsAbsolutelySummable Φ] (Λ : Finset S) :
    (∑ i ∈ Λ, Φ.normAt i) ≠ ⊤ :=
  (ENNReal.sum_lt_top.2 fun i _ ↦
    lt_top_iff_ne_top.2 (IsAbsolutelySummable.normAt_ne_top (Φ := Φ) i)).ne

lemma tsum_termNorm_ne_top [IsAbsolutelySummable Φ] (Λ : Finset S) :
    ∑' A : Finset S, Φ.termNorm Λ A ≠ ⊤ :=
  ne_of_lt (lt_of_le_of_lt (tsum_termNorm_le (Φ := Φ) Λ)
    (lt_top_iff_ne_top.2 (sum_normAt_ne_top (Φ := Φ) Λ)))

lemma termNorm_ne_top [IsAbsolutelySummable Φ] (Λ A : Finset S) : Φ.termNorm Λ A ≠ ⊤ :=
  ENNReal.ne_top_of_tsum_ne_top (tsum_termNorm_ne_top (Φ := Φ) Λ) A

lemma abs_hamiltonianTerms_le_termNorm_toReal [IsAbsolutelySummable Φ]
    (Λ : Finset S) (η : S → E) (A : Finset S) :
    ‖Φ.hamiltonianTerms Λ η A‖ ≤ (Φ.termNorm Λ A).toReal := by
  have h := enorm_hamiltonianTerms_le_termNorm (Φ := Φ) Λ η A
  rw [← ENNReal.toReal_le_toReal (by simp) (termNorm_ne_top (Φ := Φ) Λ A)] at h
  simpa [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (norm_nonneg _)] using h

/-- The total variation of the Hamiltonian series in `Λ` is bounded by `∑_{i ∈ Λ} ‖Φ‖ᵢ`. -/
lemma tsum_enorm_hamiltonianTerms_le (Λ : Finset S) (η : S → E) :
    ∑' A : Finset S, ‖Φ.hamiltonianTerms Λ η A‖ₑ ≤ ∑ i ∈ Λ, Φ.normAt i :=
  le_trans (ENNReal.tsum_le_tsum (enorm_hamiltonianTerms_le_termNorm (Φ := Φ) Λ η))
    (tsum_termNorm_le (Φ := Φ) Λ)

/-- An absolutely summable potential is summable. -/
lemma summable_hamiltonianTerms [IsAbsolutelySummable Φ] (Λ : Finset S) (η : S → E) :
    Summable (Φ.hamiltonianTerms Λ η) :=
  Summable.of_enorm (ne_of_lt (lt_of_le_of_lt (tsum_enorm_hamiltonianTerms_le Λ η)
    (lt_top_iff_ne_top.2 (sum_normAt_ne_top (Φ := Φ) Λ))))

instance (priority := 100) IsAbsolutelySummable.isSummable [IsAbsolutelySummable Φ] :
    IsSummable Φ where
  summable Λ η := (summable_hamiltonianTerms (Φ := Φ) Λ η).powerset

/-- The Hamiltonian of an absolutely summable potential is the unconditional sum. -/
lemma hamiltonian_eq_tsum [IsAbsolutelySummable Φ] (Λ : Finset S) (η : S → E) :
    Φ.hamiltonian Λ η = ∑' A : Finset S, Φ.hamiltonianTerms Λ η A :=
  ((summable_hamiltonianTerms (Φ := Φ) Λ η).hasSum.powerset).tsum_eq

lemma tendstoUniformly_sum_hamiltonianTerms [IsAbsolutelySummable Φ] (Λ : Finset S) :
    TendstoUniformly (fun s : Finset (Finset S) ↦ fun η ↦ ∑ A ∈ s, Φ.hamiltonianTerms Λ η A)
      (Φ.hamiltonian Λ) atTop := by
  have h := tendstoUniformly_tsum
    (ENNReal.summable_toReal (tsum_termNorm_ne_top (Φ := Φ) Λ))
    (fun A η ↦ abs_hamiltonianTerms_le_termNorm_toReal (Φ := Φ) Λ η A)
  rw [← tendstoUniformlyOn_univ] at h ⊢
  exact h.congr_right fun η _ ↦ (hamiltonian_eq_tsum (Φ := Φ) Λ η).symm

lemma hasSumUniformly_hamiltonianTerms [IsAbsolutelySummable Φ] (Λ : Finset S) :
    HasSumUniformly (fun A η ↦ Φ.hamiltonianTerms Λ η A) (Φ.hamiltonian Λ) :=
  hasSumUniformly_iff_tendstoUniformly.2 (tendstoUniformly_sum_hamiltonianTerms (Φ := Φ) Λ)

instance (priority := 100) IsAbsolutelySummable.isUniformlyConvergent [IsAbsolutelySummable Φ] :
    IsUniformlyConvergent Φ where
  tendstoUniformly Λ :=
    (tendstoUniformly_sum_hamiltonianTerms (Φ := Φ) Λ).comp_tendsto
      Filter.tendsto_finset_powerset_atTop_atTop

/-- `‖H_Λ^Φ‖ ≤ ∑_{i ∈ Λ} ‖Φ‖ᵢ`. -/
theorem enorm_hamiltonian_le [IsAbsolutelySummable Φ] (Λ : Finset S) (η : S → E) :
    ‖Φ.hamiltonian Λ η‖ₑ ≤ ∑ i ∈ Λ, Φ.normAt i := by
  rw [hamiltonian_eq_tsum (Φ := Φ) Λ η]
  exact le_trans enorm_tsum_le_tsum_enorm (tsum_enorm_hamiltonianTerms_le Λ η)

/-- The Hamiltonian bound in sup-norm form. -/
theorem iSup_enorm_hamiltonian_le [IsAbsolutelySummable Φ] (Λ : Finset S) :
    ⨆ η, ‖Φ.hamiltonian Λ η‖ₑ ≤ ∑ i ∈ Λ, Φ.normAt i :=
  iSup_le fun η ↦ enorm_hamiltonian_le (Φ := Φ) Λ η

/-- The Hamiltonian bound in real form. -/
lemma abs_hamiltonian_le [IsAbsolutelySummable Φ] (Λ : Finset S) (η : S → E) :
    |Φ.hamiltonian Λ η| ≤ (∑ i ∈ Λ, Φ.normAt i).toReal := by
  have h := enorm_hamiltonian_le (Φ := Φ) Λ η
  rw [← ENNReal.toReal_le_toReal (by simp) (sum_normAt_ne_top (Φ := Φ) Λ)] at h
  simpa [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)] using h

/-- Absolute summability bounds every interaction term whose support is nonempty. The empty
support never appears in any `normAt i`, so this does not constrain `Φ ∅`. -/
lemma IsAbsolutelySummable.iSup_enorm_ne_top [IsAbsolutelySummable Φ] {A : Finset S}
    (hA : A.Nonempty) : ⨆ η, ‖Φ A η‖ₑ ≠ ⊤ := by
  obtain ⟨i, hi⟩ := hA
  have hterm := ENNReal.ne_top_of_tsum_ne_top
    (IsAbsolutelySummable.normAt_ne_top (Φ := Φ) i) A
  rwa [Set.indicator_of_mem (show A ∈ {B : Finset S | i ∈ B} from hi)] at hterm

lemma IsFiniteRange.normAt_eq_sum [IsFiniteRange Φ] (i : S) {Δ : Finset S}
    (hΔ : ∀ A : Finset S, i ∈ A → Φ A ≠ 0 → A ⊆ Δ) :
    Φ.normAt i =
      ∑ A ∈ Δ.powerset, {A : Finset S | i ∈ A}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) A := by
  refine tsum_eq_sum fun A hA ↦ ?_
  by_cases hi : i ∈ A
  · rw [Set.indicator_of_mem (show A ∈ {B : Finset S | i ∈ B} from hi)]
    by_cases hΦ : Φ A = 0
    · simp [hΦ]
    · exact (hA (Finset.mem_powerset.2 (hΔ A hi hΦ))).elim
  · rw [Set.indicator_of_notMem (show A ∉ {B : Finset S | i ∈ B} from hi)]

/-- A finite range potential is absolutely summable as soon as every term on a nonempty support
is bounded. -/
lemma IsFiniteRange.isAbsolutelySummable [IsFiniteRange Φ]
    (h : ∀ A : Finset S, A.Nonempty → ⨆ η, ‖Φ A η‖ₑ ≠ ⊤) : IsAbsolutelySummable Φ where
  normAt_ne_top i := by
    obtain ⟨Δ, hΔ⟩ := IsFiniteRange.exists_finset (Φ := Φ) i
    rw [IsFiniteRange.normAt_eq_sum (Φ := Φ) i hΔ]
    refine (ENNReal.sum_lt_top.2 fun A _ ↦ ?_).ne
    by_cases hi : i ∈ A
    · rw [Set.indicator_of_mem (show A ∈ {B : Finset S | i ∈ B} from hi)]
      exact lt_top_iff_ne_top.2 (h A ⟨i, hi⟩)
    · rw [Set.indicator_of_notMem (show A ∉ {B : Finset S | i ∈ B} from hi)]
      exact ENNReal.zero_lt_top

/-- For finite range potentials, absolute summability is boundedness of the nonempty terms. -/
lemma IsFiniteRange.isAbsolutelySummable_iff [IsFiniteRange Φ] :
    IsAbsolutelySummable Φ ↔ ∀ A : Finset S, A.Nonempty → ⨆ η, ‖Φ A η‖ₑ ≠ ⊤ :=
  ⟨fun _ _ hA ↦ IsAbsolutelySummable.iSup_enorm_ne_top hA,
    IsFiniteRange.isAbsolutelySummable⟩

/-! ### Truncation and density in the interaction seminorms -/

lemma iSup_enorm_truncation_le (Δ B : Finset S) :
    ⨆ η, ‖Φ.truncation Δ B η‖ₑ ≤ ⨆ η, ‖Φ B η‖ₑ := by
  classical
  refine iSup_le fun η ↦ ?_
  by_cases h : B ⊆ Δ
  · rw [truncation_of_subset h]
    exact le_iSup (fun ζ ↦ ‖Φ B ζ‖ₑ) η
  · rw [truncation_of_not_subset h]
    simp

lemma normAt_truncation_le (Δ : Finset S) (i : S) :
    (Φ.truncation Δ).normAt i ≤ Φ.normAt i := by
  refine ENNReal.tsum_le_tsum fun B ↦ ?_
  by_cases hi : B ∈ {A : Finset S | i ∈ A}
  · rw [Set.indicator_of_mem hi, Set.indicator_of_mem hi]
    exact iSup_enorm_truncation_le Δ B
  · rw [Set.indicator_of_notMem hi, Set.indicator_of_notMem hi]

instance (Δ : Finset S) [IsAbsolutelySummable Φ] : IsAbsolutelySummable (Φ.truncation Δ) where
  normAt_ne_top i := ne_top_of_le_ne_top (IsAbsolutelySummable.normAt_ne_top (Φ := Φ) i)
    (normAt_truncation_le Δ i)

variable (Φ) in
/-- The tail `∑_{A ∩ Λ ≠ ∅, A ⊄ Δ} ‖Φ_A‖` of the interaction series in the volume `Λ`. -/
def tailWeight (Δ Λ : Finset S) : ℝ≥0∞ :=
  ∑' A : Finset S,
    {A : Finset S | ¬ Disjoint A Λ ∧ ¬ A ⊆ Δ}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) A

lemma tailWeight_le_tsum_termNorm (Δ Λ : Finset S) :
    Φ.tailWeight Δ Λ ≤ ∑' A : Finset S, Φ.termNorm Λ A := by
  refine ENNReal.tsum_le_tsum fun B ↦ ?_
  by_cases hB : B ∈ {A : Finset S | ¬ Disjoint A Λ ∧ ¬ A ⊆ Δ}
  · rw [Set.indicator_of_mem hB, termNorm_of_not_disjoint hB.1]
  · rw [Set.indicator_of_notMem hB]
    exact zero_le

lemma tailWeight_ne_top [IsAbsolutelySummable Φ] (Δ Λ : Finset S) :
    Φ.tailWeight Δ Λ ≠ ⊤ :=
  ne_top_of_le_ne_top (tsum_termNorm_ne_top (Φ := Φ) Λ) (tailWeight_le_tsum_termNorm Δ Λ)

lemma indicator_tail_eq (Δ Λ B : Finset S) :
    {A : Finset S | ¬ Disjoint A Λ ∧ ¬ A ⊆ Δ}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) B
      = {A : Finset S | A ∉ Δ.powerset}.indicator (Φ.termNorm Λ) B := by
  classical
  by_cases hsub : B ⊆ Δ
  · rw [Set.indicator_of_notMem (fun h ↦ h.2 hsub),
      Set.indicator_of_notMem
        (show B ∉ {A : Finset S | A ∉ Δ.powerset} from
          fun h ↦ h (Finset.mem_powerset.2 hsub))]
  · rw [Set.indicator_of_mem
      (show B ∈ {A : Finset S | A ∉ Δ.powerset} from fun h ↦ hsub (Finset.mem_powerset.1 h))]
    by_cases hd : Disjoint B Λ
    · rw [Set.indicator_of_notMem (fun h ↦ h.1 hd), termNorm_of_disjoint hd]
    · rw [Set.indicator_of_mem
        (show B ∈ {A : Finset S | ¬ Disjoint A Λ ∧ ¬ A ⊆ Δ} from ⟨hd, hsub⟩),
        termNorm_of_not_disjoint hd]

lemma tailWeight_eq_tsum_compl (Δ Λ : Finset S) :
    Φ.tailWeight Δ Λ
      = ∑' B : {A : Finset S // A ∉ Δ.powerset}, Φ.termNorm Λ (B : Finset S) :=
  calc Φ.tailWeight Δ Λ
      = ∑' B : Finset S, {A : Finset S | A ∉ Δ.powerset}.indicator (Φ.termNorm Λ) B :=
        tsum_congr fun B ↦ indicator_tail_eq Δ Λ B
    _ = ∑' B : {A : Finset S // A ∉ Δ.powerset}, Φ.termNorm Λ (B : Finset S) :=
        (tsum_subtype {A : Finset S | A ∉ Δ.powerset} (Φ.termNorm Λ)).symm

theorem tendsto_tailWeight_atTop [IsAbsolutelySummable Φ] (Λ : Finset S) :
    Tendsto (fun Δ : Finset S ↦ Φ.tailWeight Δ Λ) atTop (𝓝 0) := by
  have hfun : (fun Δ : Finset S ↦ Φ.tailWeight Δ Λ)
      = fun Δ : Finset S ↦
          ∑' B : {A : Finset S // A ∉ Δ.powerset}, Φ.termNorm Λ (B : Finset S) :=
    funext fun Δ ↦ tailWeight_eq_tsum_compl Δ Λ
  rw [hfun]
  have h := (ENNReal.tendsto_tsum_compl_atTop_zero (f := Φ.termNorm Λ)
    (tsum_termNorm_ne_top (Φ := Φ) Λ)).comp
    (Filter.tendsto_finset_powerset_atTop_atTop (α := S))
  simpa [Function.comp_def] using h

lemma normAt_sub_truncation (Δ : Finset S) (i : S) :
    (Φ - Φ.truncation Δ).normAt i = Φ.tailWeight Δ {i} := by
  classical
  unfold normAt tailWeight
  refine tsum_congr fun A ↦ ?_
  by_cases hi : i ∈ A
  · have hmem : A ∈ {A : Finset S | i ∈ A} := hi
    rw [Set.indicator_of_mem hmem]
    by_cases hAΔ : A ⊆ Δ
    · have hnot : A ∉ {A : Finset S | ¬ Disjoint A {i} ∧ ¬ A ⊆ Δ} := fun h ↦ h.2 hAΔ
      rw [Set.indicator_of_notMem hnot]
      simp [Pi.sub_apply, truncation_of_subset hAΔ]
    · have hm : A ∈ {A : Finset S | ¬ Disjoint A {i} ∧ ¬ A ⊆ Δ} :=
        ⟨by simpa [Finset.disjoint_singleton_right] using hi, hAΔ⟩
      rw [Set.indicator_of_mem hm]
      simp [Pi.sub_apply, truncation_of_not_subset hAΔ]
  · have hnm : A ∉ {A : Finset S | i ∈ A} := hi
    have hnm' : A ∉ {A : Finset S | ¬ Disjoint A {i} ∧ ¬ A ⊆ Δ} := fun h ↦
      h.1 (by simpa [Finset.disjoint_singleton_right] using hi)
    rw [Set.indicator_of_notMem hnm, Set.indicator_of_notMem hnm']

/-- The truncations `Φ^Δ` of an absolutely summable potential converge to `Φ` in every
interaction seminorm. -/
theorem tendsto_normAt_sub_truncation [IsAbsolutelySummable Φ] (i : S) :
    Tendsto (fun Δ : Finset S ↦ (Φ - Φ.truncation Δ).normAt i) atTop (𝓝 0) := by
  simpa [normAt_sub_truncation] using tendsto_tailWeight_atTop (Φ := Φ) {i}

end Potential
