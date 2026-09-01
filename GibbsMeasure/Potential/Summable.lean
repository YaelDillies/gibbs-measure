/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import GibbsMeasure.Potential
public import GibbsMeasure.Specification
public import GibbsMeasure.Mathlib.Logic.Function.DependsOn
public import GibbsMeasure.Mathlib.Topology.Algebra.InfiniteSum.Volume
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Potentials and their Hamiltonians

An interaction potential (`Potential.IsPotential`) is summable when the Hamiltonian series
`H_Λ = ∑_{A ∩ Λ ≠ ∅} Φ_A` converges along `SummationFilter.volume` (`Potential.IsSummable`).
Finite range is the special case in which the series has finite support.

## Main results

* `Potential.hamiltonian_sub`: the Hamiltonian difference as a series, and
  `Potential.dependsOn_hamiltonian_sub` / `Potential.measurable_hamiltonian_sub`.
* `Potential.isPremodifier_boltzmannFactor`: Boltzmann factors form a pre-modification.
  Countability of `S` is used only for measurability of the infinite Hamiltonian;
  `isPremodifier_boltzmannFactor_of_measurable` and
  `isPremodifier_boltzmannFactor_of_isFiniteRange` drop it.
* `Potential.IsAbsolutelySummable`: absolute summability, with `‖Φ‖ᵢ` as `Potential.normAt`; it
  implies `IsSummable` and bounds the Hamiltonian. Finite range potentials are absolutely
  summable iff every term on a nonempty support is bounded
  (`IsFiniteRange.isAbsolutelySummable_iff`).
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

/-- Summability of the Hamiltonian series along `SummationFilter.volume`. -/
class IsSummable (Φ : Potential S E) : Prop where
  summable (Λ : Finset S) (η : S → E) :
    Summable (Φ.hamiltonianTerms Λ η) (SummationFilter.volume S)

/-- The Hamiltonian in volume `Λ`. -/
def hamiltonian (Φ : Potential S E) (Λ : Finset S) (η : S → E) : ℝ :=
  ∑'[SummationFilter.volume S] A, Φ.hamiltonianTerms Λ η A

lemma hasSum_hamiltonian [IsSummable Φ] (Λ : Finset S) (η : S → E) :
    HasSum (Φ.hamiltonianTerms Λ η) (Φ.hamiltonian Λ η) (SummationFilter.volume S) :=
  (IsSummable.summable Λ η).hasSum

/-- Unconditional summability of the interaction terms suffices. -/
lemma IsSummable.of_summable (h : ∀ (Λ : Finset S) (η : S → E), Summable (Φ.hamiltonianTerms Λ η)) :
    IsSummable Φ where
  summable Λ η := (h Λ η).volume

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
      (SummationFilter.volume S) := by
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
  exact hsum ▸ h.volume

instance (priority := 100) IsFiniteRange.isSummable [IsFiniteRange Φ] : IsSummable Φ where
  summable Λ η := ⟨_, hasSum_interactingHamiltonian (Φ := Φ) Λ η⟩

@[simp] lemma hamiltonian_eq_interactingHamiltonian [IsFiniteRange Φ]
    (Λ : Finset S) (η : S → E) :
    Φ.hamiltonian Λ η = interactingHamiltonian (Φ := Φ) Λ η :=
  (hasSum_interactingHamiltonian (Φ := Φ) Λ η).tsum_eq

/-! ### Hamiltonian differences -/

/-- The terms of `H_Λ₂ - H_Λ₁`, for `Λ₁ ⊆ Λ₂`. -/
lemma hamiltonianTerms_sub (hΛ : Λ₁ ⊆ Λ₂) (η : S → E) :
    Φ.hamiltonianTerms Λ₂ η - Φ.hamiltonianTerms Λ₁ η
      = {A : Finset S | ¬ Disjoint A Λ₂ ∧ Disjoint A Λ₁}.indicator fun A ↦ Φ A η := by
  funext A
  by_cases h₁ : Disjoint A Λ₁
  · by_cases h₂ : Disjoint A Λ₂
    · simp [hamiltonianTerms, Set.indicator_of_notMem, h₁, h₂, not_not]
    · rw [Pi.sub_apply, hamiltonianTerms_of_not_disjoint h₂, hamiltonianTerms_of_disjoint h₁,
        Set.indicator_of_mem (show A ∈ {A : Finset S | ¬ Disjoint A Λ₂ ∧ Disjoint A Λ₁} from
          ⟨h₂, h₁⟩), sub_zero]
  · have h₂ : ¬ Disjoint A Λ₂ := fun h ↦ h₁ (h.mono_right hΛ)
    rw [Pi.sub_apply, hamiltonianTerms_of_not_disjoint h₂, hamiltonianTerms_of_not_disjoint h₁,
      Set.indicator_of_notMem (show A ∉ {A : Finset S | ¬ Disjoint A Λ₂ ∧ Disjoint A Λ₁} from
        fun h ↦ h₁ h.2), sub_self]

lemma hasSum_hamiltonianTerms_sub [IsSummable Φ] (hΛ : Λ₁ ⊆ Λ₂) (η : S → E) :
    HasSum ({A : Finset S | ¬ Disjoint A Λ₂ ∧ Disjoint A Λ₁}.indicator fun A ↦ Φ A η)
      (Φ.hamiltonian Λ₂ η - Φ.hamiltonian Λ₁ η) (SummationFilter.volume S) :=
  hamiltonianTerms_sub (Φ := Φ) hΛ η ▸
    (hasSum_hamiltonian (Φ := Φ) Λ₂ η).sub (hasSum_hamiltonian (Φ := Φ) Λ₁ η)

/-- For `Λ₁ ⊆ Λ₂`,
`H_Λ₂ - H_Λ₁ = ∑_{A ∩ Λ₂ ≠ ∅, A ∩ Λ₁ = ∅} Φ_A`. -/
lemma hamiltonian_sub [IsSummable Φ] (hΛ : Λ₁ ⊆ Λ₂) (η : S → E) :
    Φ.hamiltonian Λ₂ η - Φ.hamiltonian Λ₁ η =
      ∑'[SummationFilter.volume S] A,
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
  DependsOn.of_tendsto (l := (SummationFilter.volume S).filter)
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
  measurable_of_tendsto_metrizable' (SummationFilter.volume S).filter
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
      ENNReal.ofReal (Real.exp a) * ENNReal.ofReal (Real.exp b) :=
  (Real.exp_add a b).symm ▸ ENNReal.ofReal_mul (Real.exp_nonneg a)

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

lemma enorm_hamiltonianTerms_le_termNorm (Λ : Finset S) (η : S → E) (A : Finset S) :
    ‖Φ.hamiltonianTerms Λ η A‖ₑ ≤ Φ.termNorm Λ A := by
  by_cases h : Disjoint A Λ
  · have hnm : A ∉ {B : Finset S | ¬ Disjoint B Λ} := by simpa using h
    simp [hamiltonianTerms_of_disjoint h, termNorm, Set.indicator_of_notMem hnm]
  · rw [hamiltonianTerms_of_not_disjoint h, termNorm,
      Set.indicator_of_mem (show A ∈ {B : Finset S | ¬ Disjoint B Λ} from h)]
    exact le_iSup (fun η ↦ ‖Φ A η‖ₑ) η

lemma termNorm_le_sum (Λ : Finset S) (A : Finset S) :
    Φ.termNorm Λ A ≤ ∑ i ∈ Λ, {A : Finset S | i ∈ A}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) A := by
  by_cases h : Disjoint A Λ
  · have hnm : A ∉ {B : Finset S | ¬ Disjoint B Λ} := by simpa using h
    simp [termNorm, Set.indicator_of_notMem hnm]
  · obtain ⟨i, hiA, hiΛ⟩ := Finset.not_disjoint_iff.1 h
    refine le_trans ?_ (Finset.single_le_sum (f := fun i ↦
      {A : Finset S | i ∈ A}.indicator (fun A ↦ ⨆ η, ‖Φ A η‖ₑ) A) (fun _ _ ↦ bot_le) hiΛ)
    rw [termNorm, Set.indicator_of_mem (show A ∈ {B : Finset S | ¬ Disjoint B Λ} from h),
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

/-- The total variation of the Hamiltonian series in `Λ` is bounded by `∑_{i ∈ Λ} ‖Φ‖ᵢ`. -/
lemma tsum_enorm_hamiltonianTerms_le (Λ : Finset S) (η : S → E) :
    ∑' A : Finset S, ‖Φ.hamiltonianTerms Λ η A‖ₑ ≤ ∑ i ∈ Λ, Φ.normAt i :=
  le_trans (ENNReal.tsum_le_tsum (enorm_hamiltonianTerms_le_termNorm (Φ := Φ) Λ η))
    (tsum_termNorm_le (Φ := Φ) Λ)

/-- An absolutely summable potential is summable. -/
lemma summable_hamiltonianTerms [IsAbsolutelySummable Φ] (Λ : Finset S) (η : S → E) :
    Summable (Φ.hamiltonianTerms Λ η) := by
  exact Summable.of_enorm (ne_of_lt (lt_of_le_of_lt (tsum_enorm_hamiltonianTerms_le Λ η)
    (lt_top_iff_ne_top.2 (sum_normAt_ne_top (Φ := Φ) Λ))))

instance (priority := 100) IsAbsolutelySummable.isSummable [IsAbsolutelySummable Φ] :
    IsSummable Φ where
  summable Λ η := (summable_hamiltonianTerms (Φ := Φ) Λ η).volume

/-- The Hamiltonian of an absolutely summable potential is the unconditional sum. -/
lemma hamiltonian_eq_tsum [IsAbsolutelySummable Φ] (Λ : Finset S) (η : S → E) :
    Φ.hamiltonian Λ η = ∑' A : Finset S, Φ.hamiltonianTerms Λ η A :=
  ((summable_hamiltonianTerms (Φ := Φ) Λ η).hasSum.volume).tsum_eq

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
    · rw [hΦ]; simp
    · exact (hA (Finset.mem_powerset.2 (hΔ A hi hΦ))).elim
  · exact Set.indicator_of_notMem (show A ∉ {B : Finset S | i ∈ B} from hi)

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
      exact (h A ⟨i, hi⟩).lt_top
    · rw [Set.indicator_of_notMem (show A ∉ {B : Finset S | i ∈ B} from hi)]
      exact ENNReal.zero_lt_top

/-- For finite range potentials, absolute summability is boundedness of the nonempty terms. -/
lemma IsFiniteRange.isAbsolutelySummable_iff [IsFiniteRange Φ] :
    IsAbsolutelySummable Φ ↔ ∀ A : Finset S, A.Nonempty → ⨆ η, ‖Φ A η‖ₑ ≠ ⊤ :=
  ⟨fun _ A hA ↦ IsAbsolutelySummable.iSup_enorm_ne_top hA,
    IsFiniteRange.isAbsolutelySummable⟩

end Potential
