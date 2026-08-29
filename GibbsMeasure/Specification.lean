/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Matteo Cipollina
-/
module

public import GibbsMeasure.Mathlib.MeasureTheory.Constructions.Cylinders
public import GibbsMeasure.Mathlib.MeasureTheory.Measure.Ext
public import GibbsMeasure.Mathlib.MeasureTheory.Measure.GiryMonad
public import GibbsMeasure.Prereqs.Filtration.Consistent
public import GibbsMeasure.Prereqs.Juxt
public import GibbsMeasure.Prereqs.Kernel.CondExp
public import Mathlib.Probability.ProductMeasure

/-!
# Gibbs measures

This file defines Gibbs measures.
-/

@[expose] public section

open ProbabilityTheory Set MeasureTheory ENNReal NNReal

variable {S E : Type*} {mE : MeasurableSpace E} {Λ₁ Λ₂ : Finset S}

/-- A family of kernels `γ` is consistent if `γ Λ₁ ∘ₖ γ Λ₂ = γ Λ₂` for all `Λ₁ ⊆ Λ₂`.

Morally, the LHS should be thought of as discovering `Λ₁` then `Λ₂`, while the RHS should be
thought of as discovering `Λ₂` straight away. -/
def IsConsistent (γ : ∀ Λ : Finset S, Kernel[cylinderEvents Λᶜ] (S → E) (S → E)) : Prop :=
  ∀ ⦃Λ₁ Λ₂⦄, Λ₁ ⊆ Λ₂ → (γ Λ₁).comap id cylinderEvents_le_pi ∘ₖ γ Λ₂ = γ Λ₂

lemma isConsistentKernel_cylinderEventsCompl
    {γ : ∀ Λ : Finset S, Kernel[cylinderEvents Λᶜ] (S → E) (S → E)} :
    Filtration.cylinderEventsCompl.IsConsistentKernel (fun Λ ↦ γ (OrderDual.ofDual Λ)) ↔
      IsConsistent γ := forall_comm

variable (S E) in
/-- A specification from `S` to `E` is a collection of "boundary condition kernels" on the
complement of finite sets, compatible under restriction.

The term "boundary condition kernels" is chosen because for a Gibbs measure associated to
a specification, the kernels of the specification are precisely the regular conditional
probabilities of the Gibbs measure conditionally on the configurations in the complements of
finite sets (which serve as "boundary conditions"). -/
structure Specification [MeasurableSpace E] where
  /-- The boundary condition kernels of a specification.

  DO NOT USE. Instead use the coercion to function `⇑γ`. Lean should insert it automatically in most
  cases. -/
  toFun (Λ : Finset S) : Kernel[cylinderEvents Λᶜ] (S → E) (S → E)
  /-- The boundary condition kernels of a specification are consistent.

  DO NOT USE. Instead use `Specification.isConsistent`. -/
  isConsistent' : IsConsistent toFun

namespace Specification

instance instDFunLike :
    DFunLike (Specification S E) (Finset S) fun Λ ↦ Kernel[cylinderEvents Λᶜ] (S → E) (S → E)
    where
  coe := toFun
  coe_injective γ₁ γ₂ h := by cases γ₁; cases γ₂; congr

/-- The boundary condition kernels of a specification are consistent. -/
lemma isConsistent (γ : Specification S E) : IsConsistent γ := γ.isConsistent'

initialize_simps_projections Specification (toFun → apply)

variable {γ γ₁ γ₂ : Specification S E} {Λ Λ₁ Λ₂ : Finset S}

@[ext] lemma ext : (∀ Λ, γ₁ Λ = γ₂ Λ) → γ₁ = γ₂ := DFunLike.ext _ _

protected lemma bind (hΛ : Λ₁ ⊆ Λ₂) (η : S → E) : (γ Λ₂ η).bind (γ Λ₁) = γ Λ₂ η :=
  DFunLike.congr_fun (γ.isConsistent hΛ) η

section IsIndep

/-- An independent specification is a specification `γ` where `γ Λ₁ ∘ₖ γ Λ₂ = γ (Λ₁ ∪ Λ₂)` for all
`Λ₁ Λ₂`. -/
def IsIndep (γ : Specification S E) : Prop :=
  ∀ ⦃Λ₁ Λ₂⦄ [DecidableEq S] , (γ Λ₁).comap id cylinderEvents_le_pi ∘ₖ γ Λ₂ = (γ (Λ₁ ∪ Λ₂)).comap id
      (measurable_id'' <| by gcongr; exact Finset.subset_union_right)

end IsIndep

section IsMarkov

/-- A Markov specification is a specification whose boundary condition kernels are all Markov
kernels. -/
class IsMarkov (γ : Specification S E) : Prop where
  isMarkovKernel : ∀ Λ, IsMarkovKernel (γ Λ)

instance IsMarkov.toIsMarkovKernel [γ.IsMarkov] {Λ : Finset S} : IsMarkovKernel (γ Λ) :=
  isMarkovKernel _

end IsMarkov

section IsProper

/-- A specification is proper if all its boundary condition kernels are. -/
def IsProper (γ : Specification S E) : Prop := ∀ Λ : Finset S, (γ Λ).IsProper

lemma isProper_iff_restrict_eq_indicator_smul :
    γ.IsProper ↔
      ∀ (Λ : Finset S) ⦃B : Set (S → E)⦄ (hB : MeasurableSet[cylinderEvents Λᶜ] B) (x : S → E),
      (γ Λ).restrict (cylinderEvents_le_pi _ hB) x = B.indicator (1 : (S → E) → ℝ≥0∞) x • γ Λ x :=
  forall_congr' fun _ ↦ Kernel.isProper_iff_restrict_eq_indicator_smul _

lemma isProper_iff_inter_eq_indicator_mul :
    γ.IsProper ↔
      ∀ (Λ : Finset S) ⦃A : Set (S → E)⦄ (_hA : MeasurableSet A) ⦃B : Set (S → E)⦄
        (_hB : MeasurableSet[cylinderEvents Λᶜ] B) (η : S → E),
      γ Λ η (A ∩ B) = B.indicator 1 η * γ Λ η A :=
  forall_congr' fun _ ↦ Kernel.isProper_iff_inter_eq_indicator_mul cylinderEvents_le_pi

alias ⟨IsProper.restrict_eq_indicator_smul, IsProper.of_restrict_eq_indicator_smul⟩ :=
  isProper_iff_restrict_eq_indicator_smul

alias ⟨IsProper.inter_eq_indicator_mul, IsProper.of_inter_eq_indicator_mul⟩ :=
  isProper_iff_inter_eq_indicator_mul

variable {A B : Set (S → E)} {f g : (S → E) → ℝ≥0∞} {η₀ : S → E}

lemma IsProper.setLIntegral_eq_indicator_mul_lintegral (hγ : γ.IsProper) (Λ : Finset S)
    (hf : Measurable f) (hB : MeasurableSet[cylinderEvents Λᶜ] B) :
    ∫⁻ x in B, f x ∂(γ Λ η₀) = B.indicator 1 η₀ * ∫⁻ x, f x ∂(γ Λ η₀) :=
  (hγ Λ).setLIntegral_eq_indicator_mul_lintegral cylinderEvents_le_pi hf hB _

lemma IsProper.setLIntegral_inter_eq_indicator_mul_setLIntegral (Λ : Finset S) (hγ : γ.IsProper)
    (hf : Measurable f) (hA : MeasurableSet A) (hB : MeasurableSet[cylinderEvents Λᶜ] B) :
    ∫⁻ x in A ∩ B, f x ∂(γ Λ η₀) = B.indicator 1 η₀ * ∫⁻ x in A, f x ∂(γ Λ η₀) :=
  (hγ Λ).setLIntegral_inter_eq_indicator_mul_setLIntegral cylinderEvents_le_pi hf hA hB _

lemma IsProper.lintegral_mul (hγ : γ.IsProper) (Λ : Finset S) (hf : Measurable f)
    (hg : Measurable[cylinderEvents Λᶜ] g) :
    ∫⁻ x, g x * f x ∂(γ Λ η₀) = g η₀ * ∫⁻ x, f x ∂(γ Λ η₀) :=
  (hγ _).lintegral_mul cylinderEvents_le_pi hf hg _

end IsProper

section IsGibbsMeasure
variable {μ : Measure (S → E)}

/-- For a specification `γ`, a Gibbs measure is a measure whose conditional expectation kernels
conditionally on configurations exterior to finite sets agree with the boundary condition kernels
of the specification `γ`. -/
def IsGibbsMeasure (γ : Specification S E) (μ : Measure (S → E)) : Prop := ∀ Λ, (γ Λ).IsCondExp μ

-- The following two lemmas should generalise to a family of kernels indexed by a filtration
lemma isGibbsMeasure_iff_forall_bind_eq (hγ : γ.IsProper) [IsFiniteMeasure μ] :
    γ.IsGibbsMeasure μ ↔ ∀ Λ, μ.bind (γ Λ) = μ :=
  forall_congr' fun _Λ ↦ Kernel.isCondExp_iff_bind_eq_left (hγ _) cylinderEvents_le_pi

lemma isGibbsMeasure_iff_frequently_bind_eq (hγ : γ.IsProper) [IsFiniteMeasure μ] [IsMarkov γ] :
    γ.IsGibbsMeasure μ ↔ ∃ᶠ Λ in .atTop, μ.bind (γ Λ) = μ := by
  classical
  rw [isGibbsMeasure_iff_forall_bind_eq hγ]
  refine ⟨Filter.Frequently.of_forall, fun h Λ ↦ ?_⟩
  obtain ⟨Λ', h, hΛ'⟩ := h.forall_exists_of_atTop Λ
  rw [← hΛ', Measure.bind_bind, funext (γ.bind h)] <;>
    exact ((γ _).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable

end IsGibbsMeasure

noncomputable section ISSSD

private lemma setOf_mem_of_notMem_eq_pi_sdiff [DecidableEq S] (Λ s : Finset S)
    (t : S → Set E) :
    {η : S → E | ∀ i ∈ s, i ∉ Λ → η i ∈ t i} =
      ((s \ Λ : Finset S) : Set S).pi t := by
  ext η; simp [mem_pi]

private lemma measurableSet_setOf_mem_of_notMem (Λ s : Finset S)
    {t : S → Set E} (ht : ∀ i, MeasurableSet (t i)) :
    MeasurableSet[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)ᶜ]
      {η : S → E | ∀ i ∈ s, i ∉ Λ → η i ∈ t i} := by
  classical
  have : {η : S → E | ∀ i ∈ s, i ∉ Λ → η i ∈ t i} =
      ⋂ i ∈ s \ Λ, (fun η : S → E ↦ η i) ⁻¹' t i := by
    ext η
    simp [mem_iInter, Finset.mem_sdiff]
  rw [this]
  exact Finset.measurableSet_biInter
    (m := cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)ᶜ) (s \ Λ) fun i hi ↦
    (ht i).preimage <| measurable_cylinderEvent_apply (X := fun _ : S ↦ E)
      (Set.mem_compl (Finset.mem_sdiff.1 hi).2)

private lemma preimage_juxt_pi [DecidableEq S] {Λ s : Finset S} {t : S → Set E}
    {η : S → E} (hP : ∀ i ∈ s, i ∉ Λ → η i ∈ t i) :
    juxt (Λ : Set S) η ⁻¹' (s : Set S).pi t =
      univ.pi fun j : Λ ↦ if (j : S) ∈ s then t j else univ := by
  ext ζ
  simp only [mem_preimage, mem_pi]
  constructor
  · intro h j
    by_cases hjs : (j : S) ∈ s
    · simpa [hjs, juxt_apply_of_mem j.property] using h _ hjs
    · simp [hjs]
  · intro h i hi
    by_cases hiΛ : i ∈ (Λ : Set S)
    · have hi' : (⟨i, hiΛ⟩ : Λ).val ∈ s := hi
      simpa [juxt_apply_of_mem hiΛ, hi'] using h ⟨i, hiΛ⟩
    · simpa [juxt_apply_of_not_mem hiΛ] using hP i hi hiΛ

private lemma preimage_juxt_pi_eq_empty {Λ s : Finset S} {t : S → Set E} {η : S → E}
    (hP : ¬ ∀ i ∈ s, i ∉ Λ → η i ∈ t i) :
    juxt (Λ : Set S) η ⁻¹' (s : Set S).pi t = (∅ : Set (Λ → E)) := by
  ext ζ
  simp only [mem_preimage, mem_empty_iff_false, iff_false, mem_pi]
  intro h
  push Not at hP
  obtain ⟨i, his, hiΛ, hit⟩ := hP
  exact hit <| by simpa [juxt_apply_of_not_mem hiΛ] using h i his

variable (ν : Measure E)

private lemma map_juxt_apply_pi [DecidableEq S] (Λ s : Finset S) (t : S → Set E)
    (ht : ∀ i, MeasurableSet (t i)) (η : S → E) :
    (Measure.pi fun _ : Λ ↦ ν).map (juxt Λ η) ((s : Set S).pi t) =
      {ω : S → E | ∀ i ∈ s, i ∉ Λ → ω i ∈ t i}.indicator
        (fun _ ↦ (Measure.pi fun _ : Λ ↦ ν)
          (univ.pi fun j : Λ ↦ if (j : S) ∈ s then t j else univ)) η := by
  rw [Measure.map_apply .juxt (MeasurableSet.pi s.countable_toSet fun i _ ↦ ht i)]
  by_cases hP : ∀ i ∈ s, i ∉ Λ → η i ∈ t i
  · have hmem : η ∈ {ω : S → E | ∀ i ∈ s, i ∉ Λ → ω i ∈ t i} := hP
    rw [preimage_juxt_pi hP, indicator_of_mem hmem]
  · have hmem : η ∉ {ω : S → E | ∀ i ∈ s, i ∉ Λ → ω i ∈ t i} := hP
    rw [preimage_juxt_pi_eq_empty hP, measure_empty, indicator_of_notMem hmem]

private lemma measurable_map_juxt_apply_pi (Λ s : Finset S) (t : S → Set E)
    (ht : ∀ i, MeasurableSet (t i)) :
    Measurable[cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)ᶜ] fun η : S → E ↦
      (Measure.pi fun _ : Λ ↦ ν).map (juxt Λ η) ((s : Set S).pi t) := by
  classical
  simp_rw [map_juxt_apply_pi ν Λ s t ht]
  exact Measurable.indicator (m := cylinderEvents (X := fun _ : S ↦ E) (Λ : Set S)ᶜ)
    measurable_const (measurableSet_setOf_mem_of_notMem Λ s ht)

variable [IsProbabilityMeasure ν]

private lemma measure_pi_univ_pi_ite [DecidableEq S] (Λ s : Finset S) (t : S → Set E) :
    (Measure.pi fun _ : Λ ↦ ν)
        (univ.pi fun j : Λ ↦ if (j : S) ∈ s then t j else univ) =
      ∏ i ∈ s ∩ Λ, ν (t i) := by
  rw [Measure.pi_pi]
  simp only [apply_ite, measure_univ]
  exact (Finset.prod_attach Λ fun i : S ↦ if i ∈ s then ν (t i) else 1).trans <| by
    simp [Finset.prod_ite_mem, Finset.inter_comm]

lemma measurable_isssdFun (Λ : Finset S) :
    Measurable[cylinderEvents Λᶜ]
      fun η : S → E ↦ (Measure.pi fun _ : Λ ↦ ν).map (juxt Λ η) := by
  let μ' : (S → E) → Measure (S → E) :=
    fun η ↦ (Measure.pi fun _ : Λ ↦ ν).map (juxt Λ η)
  have : ∀ η, IsProbabilityMeasure (μ' η) := inferInstance
  refine @Measurable.measure_of_isPiSystem_of_isProbabilityMeasure (S → E) (S → E)
    (cylinderEvents (Λ : Set S)ᶜ) _ μ' _ (measurableSquareCylinders S fun _ : S ↦ E)
    generateFrom_measurableSquareCylinders.symm IsPiSystem.measurableSquareCylinders ?_
  rintro A ⟨s, t, ht, rfl⟩
  exact measurable_map_juxt_apply_pi ν Λ s t fun i ↦ ht i (mem_univ _)

/-- Auxiliary definition for `Specification.isssd`. -/
@[simps -fullyApplied]
def isssdFun (Λ : Finset S) : Kernel[cylinderEvents Λᶜ] (S → E) (S → E) :=
  @Kernel.mk _ _ (_) _
    (fun η ↦ Measure.map (juxt Λ η) (Measure.pi fun _ : Λ ↦ ν))
    (measurable_isssdFun ν Λ)

instance instIsMarkovKernel_isssdFun {Λ : Finset S} : IsMarkovKernel (isssdFun ν Λ) :=
  ⟨fun _ ↦ by simp only [isssdFun_apply]; infer_instance⟩

private lemma isssdFun_comap_id (Λ : Finset S) :
    (isssdFun ν Λ).comap id cylinderEvents_le_pi =
      (isssdFun ν Λ).comap id (measurable_id'' cylinderEvents_le_pi) :=
  DFunLike.ext _ _ fun _ ↦ rfl

lemma isssdFun_apply_squareCylinder [DecidableEq S] (Λ s : Finset S) (t : S → Set E)
    (ht : ∀ i, MeasurableSet (t i)) (η : S → E) :
    isssdFun ν Λ η ((s : Set S).pi t) =
      {ω | ∀ i ∈ s, i ∉ Λ → ω i ∈ t i}.indicator
        (fun _ ↦ ∏ i ∈ s ∩ Λ, ν (t i)) η := by
  rw [isssdFun_apply, map_juxt_apply_pi ν Λ s t ht η, measure_pi_univ_pi_ite]

private lemma isssdFun_apply_pi_sdiff [DecidableEq S] (Λ₁ Λ₂ s : Finset S) (t : S → Set E)
    (ht : ∀ i, MeasurableSet (t i)) (η : S → E) :
    isssdFun ν Λ₂ η {ω : S → E | ∀ i ∈ s, i ∉ Λ₁ → ω i ∈ t i} =
      {ω | ∀ i ∈ s, i ∉ Λ₁ ∪ Λ₂ → ω i ∈ t i}.indicator
        (fun _ ↦ ∏ i ∈ s ∩ (Λ₂ \ Λ₁), ν (t i)) η := by
  rw [setOf_mem_of_notMem_eq_pi_sdiff, isssdFun_apply_squareCylinder ν Λ₂ (s \ Λ₁) t ht η]
  congr 1
  · ext ω; simp [Finset.mem_sdiff, Finset.mem_union]
  · rw [Finset.inter_comm, Finset.inter_sdiff_left_comm]

private lemma lintegral_isssdFun_apply_pi [DecidableEq S] {μ : Measure (S → E)}
    (Λ s : Finset S) (t : S → Set E) (ht : ∀ i, MeasurableSet (t i)) :
    ∫⁻ ω, isssdFun ν Λ ω ((s : Set S).pi t) ∂μ =
      (∏ i ∈ s ∩ Λ, ν (t i)) * μ {ω | ∀ i ∈ s, i ∉ Λ → ω i ∈ t i} := by
  have hP : MeasurableSet {ω : S → E | ∀ i ∈ s, i ∉ Λ → ω i ∈ t i} := by
    simpa [setOf_mem_of_notMem_eq_pi_sdiff] using
      MeasurableSet.pi (s \ Λ).countable_toSet fun i _ ↦ ht i
  simp_rw [isssdFun_apply_squareCylinder ν Λ s t ht]
  exact lintegral_indicator_const hP _

private lemma lintegral_isssdFun_apply_squareCylinder [DecidableEq S] (Λ₁ Λ₂ s : Finset S)
    (t : S → Set E) (ht : ∀ i, MeasurableSet (t i)) (η : S → E) :
    ∫⁻ b, isssdFun ν Λ₁ b ((s : Set S).pi t) ∂isssdFun ν Λ₂ η =
      isssdFun ν (Λ₁ ∪ Λ₂) η ((s : Set S).pi t) := by
  rw [lintegral_isssdFun_apply_pi ν Λ₁ s t ht, isssdFun_apply_pi_sdiff ν Λ₁ Λ₂ s t ht η,
    isssdFun_apply_squareCylinder ν (Λ₁ ∪ Λ₂) s t ht η, ← indicator_const_mul]
  congr 1
  ext
  rw [← Finset.prod_inter_mul_prod_sdiff (s ∩ (Λ₁ ∪ Λ₂)) Λ₁ fun i ↦ ν (t i)]
  congr 1
  · rw [Finset.inter_assoc, Finset.inter_eq_right.2 Finset.subset_union_left]
  · rw [Finset.inter_sdiff_assoc, Finset.union_sdiff_left]

/-- The ISSSD of a measure is strongly consistent. -/
lemma isssdFun_comp_isssdFun [DecidableEq S] (Λ₁ Λ₂ : Finset S) :
    (isssdFun ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ isssdFun ν Λ₂ =
      (isssdFun ν (Λ₁ ∪ Λ₂)).comap id
        (measurable_id'' <| by gcongr; exact Finset.subset_union_right) := by
  rw [isssdFun_comap_id]
  refine DFunLike.ext _ _ fun η ↦ ?_
  refine ext_of_generateFrom_of_isProbabilityMeasure
    (C := measurableSquareCylinders S fun _ : S ↦ E)
    generateFrom_measurableSquareCylinders.symm IsPiSystem.measurableSquareCylinders ?_
  rintro A ⟨s, t, ht, rfl⟩
  have ht' : ∀ i, MeasurableSet (t i) := fun i ↦ ht i (mem_univ _)
  rw [Kernel.comp_apply, Measure.bind_apply
    (MeasurableSet.pi s.countable_toSet fun i _ ↦ ht' i) (Kernel.aemeasurable _)]
  simp only [Kernel.comap_apply, id_eq]
  exact lintegral_isssdFun_apply_squareCylinder ν Λ₁ Λ₂ s t ht' η

/-- The **Independent Specification with Single Spin Distribution**.

This is the specification corresponding to the product measure. -/
@[simps]
def isssd : Specification S E where
  toFun := isssdFun ν
  isConsistent' Λ₁ Λ₂ hΛ := by
    classical
    rw [isssdFun_comp_isssdFun]
    ext a s _
    simp only [Kernel.comap_apply, id_eq, isssdFun_apply, Finset.coe_sort_coe]
    rw [Finset.union_eq_right.2 hΛ]

/-- The ISSSD of a measure is strongly consistent. -/
lemma isssd_comp_isssd [DecidableEq S] (Λ₁ Λ₂ : Finset S) :
    (isssd ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ isssd ν Λ₂ =
      (isssd ν (Λ₁ ∪ Λ₂)).comap id
        (measurable_id'' <| by gcongr; exact Finset.subset_union_right) :=
  isssdFun_comp_isssdFun ..

protected lemma IsIndep.isssd : (isssd (S := S) ν).IsIndep :=
  fun _ _ ↦ isssdFun_comp_isssdFun ..

protected lemma IsProper.isssd : (isssd (S := S) ν).IsProper := by
  refine .of_inter_eq_indicator_mul fun Λ A hA B hB x ↦ ?_
  simp only [isssd_apply, isssdFun_apply, Finset.coe_sort_coe]
  rw [Measure.map_apply .juxt (hA.inter (cylinderEvents_le_pi _ hB)), Measure.map_apply .juxt hA,
    Set.preimage_inter]
  by_cases hx : x ∈ B
  · have : juxt (↑Λ) x ⁻¹' B = univ := by
      ext ζ
      simpa using (mem_congr_of_measurableSet_cylinderEvents hB
        fun _ hi ↦ juxt_apply_of_not_mem hi ζ).mpr hx
    rw [this, inter_univ, indicator_of_mem hx, Pi.one_apply, one_mul]
  · have : juxt (↑Λ) x ⁻¹' B = ∅ := by
      ext ζ
      simp only [mem_preimage, mem_empty_iff_false, iff_false]
      exact fun h ↦ hx ((mem_congr_of_measurableSet_cylinderEvents hB
        fun _ hi ↦ juxt_apply_of_not_mem hi ζ).mp h)
    rw [this, inter_empty, measure_empty, indicator_of_notMem hx, zero_mul]

instance isssd.instIsMarkov : (isssd (S := S) ν).IsMarkov where
  isMarkovKernel Λ := ⟨inferInstanceAs <|
    ∀ η, IsProbabilityMeasure (.map (juxt (Λ : Set S) η) <| .pi fun _ ↦ ν)⟩

section ProductMeasure

lemma isssd_apply_squareCylinder_of_subset {Λ s : Finset S} (hs : s ⊆ Λ) (t : S → Set E)
    (ht : ∀ i, MeasurableSet (t i)) (η : S → E) :
    isssd ν Λ η ((s : Set S).pi t) = ∏ i ∈ s, ν (t i) := by
  classical
  have hmem : η ∈ {ω : S → E | ∀ i ∈ s, i ∉ Λ → ω i ∈ t i} :=
    fun i hi hΛ ↦ (hΛ (hs hi)).elim
  rw [isssd_apply, isssdFun_apply_squareCylinder ν Λ s t ht, indicator_of_mem hmem,
    Finset.inter_eq_left.2 hs]

lemma bind_isssd_apply_squareCylinder_of_subset (μ : Measure (S → E)) {Λ s : Finset S}
    (hs : s ⊆ Λ) (t : S → Set E) (ht : ∀ i, MeasurableSet (t i)) :
    μ.bind (isssd ν Λ) ((s : Set S).pi t) = μ univ * ∏ i ∈ s, ν (t i) := by
  rw [Measure.bind_apply (MeasurableSet.pi s.countable_toSet fun i _ ↦ ht i)
    ((isssd ν Λ).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable]
  simp_rw [isssd_apply_squareCylinder_of_subset ν hs t ht]
  rw [lintegral_const, mul_comm]

lemma infinitePi_bind_isssd (Λ : Finset S) :
    (Measure.infinitePi fun _ : S ↦ ν).bind (isssd ν Λ) =
      Measure.infinitePi fun _ : S ↦ ν := by
  classical
  refine Measure.eq_infinitePi (μ := fun _ : S ↦ ν) fun s t ht ↦ ?_
  rw [Measure.bind_apply (MeasurableSet.pi s.countable_toSet fun i _ ↦ ht i)
    ((isssd ν Λ).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable, isssd_apply,
    lintegral_isssdFun_apply_pi ν Λ s t ht, setOf_mem_of_notMem_eq_pi_sdiff,
    Measure.infinitePi_pi (μ := fun _ : S ↦ ν) fun i _ ↦ ht i]
  exact Finset.prod_inter_mul_prod_sdiff s Λ fun i ↦ ν (t i)

/-- The product measure `ν ^ S` is a `isssd ν`-Gibbs measure. -/
lemma isGibbsMeasure_isssd_infinitePi :
    (isssd ν).IsGibbsMeasure (.infinitePi fun _ : S ↦ ν) :=
  (isGibbsMeasure_iff_forall_bind_eq (IsProper.isssd (ν := ν))).2 fun Λ ↦
    infinitePi_bind_isssd ν Λ

lemma isGibbsMeasure_isssd_iff (μ : Measure (S → E)) [IsProbabilityMeasure μ] :
    (isssd ν).IsGibbsMeasure μ ↔ μ = Measure.infinitePi fun _ : S ↦ ν := by
  refine ⟨fun hμ ↦ ?_, fun h ↦ h ▸ isGibbsMeasure_isssd_infinitePi ν⟩
  refine Measure.eq_infinitePi (μ := fun _ : S ↦ ν) fun s t ht ↦ ?_
  rw [← (isGibbsMeasure_iff_forall_bind_eq (IsProper.isssd (ν := ν))).1 hμ s,
    bind_isssd_apply_squareCylinder_of_subset ν μ le_rfl t ht, measure_univ, one_mul]

end ProductMeasure

end ISSSD

section Modifier
variable {ρ : Finset S → (S → E) → ℝ≥0∞}

/-- The kernel of a modification specification.

Modifying the specification `γ` by a family indexed by finsets `Λ : Finset S` of densities
`ρ Λ : (S → E) → ℝ≥0∞` results in a family of kernels `γ.modificationKer ρ _ Λ` whose density is
that of `γ Λ` multiplied by `ρ Λ`.

This is an auxiliary definition for `Specification.modification`, which you should generally use
instead of `Specification.modificationKer`. -/
@[simps]
noncomputable def modificationKer (γ : ∀ Λ : Finset S, Kernel[cylinderEvents Λᶜ] (S → E) (S → E))
    (ρ : Finset S → (S → E) → ℝ≥0∞) (hρ : ∀ Λ, Measurable (ρ Λ)) (Λ : Finset S) :
    Kernel[cylinderEvents Λᶜ] (S → E) (S → E) :=
  @Kernel.mk _ _ (_) _
    (fun η ↦ (γ Λ η).withDensity (ρ Λ))
    (@Measure.measurable_of_measurable_coe _ _ _ (_) _ fun s hs ↦ by
      simp_rw [MeasureTheory.withDensity_apply _ hs]
      exact (Measure.measurable_setLIntegral (hρ _) hs).comp (γ Λ).measurable)

@[simp] lemma modificationKer_one' (γ : ∀ Λ : Finset S, Kernel[cylinderEvents Λᶜ] (S → E) (S → E)) :
    modificationKer γ (fun _Λ _η ↦ 1) (fun _Λ ↦ measurable_const) = γ := by ext Λ; simp

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma modificationKer_one (γ : ∀ Λ : Finset S, Kernel[cylinderEvents Λᶜ] (S → E) (S → E)) :
    modificationKer γ 1 (fun _Λ ↦ measurable_const) = γ := by ext Λ; simp

/-- A modifier of a specification `γ` is a family indexed by finsets `Λ : Finset S` of densities
`ρ Λ : (S → E) → ℝ≥0∞` such that:
* Each `ρ Λ` is measurable.
* `γ.modificationKer ρ` (informally, `ρ * γ`) is consistent. -/
@[mk_iff]
structure IsModifier (γ : Specification S E) (ρ : Finset S → (S → E) → ℝ≥0∞) : Prop where
  measurable Λ : Measurable (ρ Λ)
  isConsistent : IsConsistent (modificationKer γ ρ measurable)

@[simp] lemma IsModifier.one' : γ.IsModifier (fun _Λ _η ↦ 1) where
  measurable _ := measurable_const
  isConsistent := by simpa using γ.isConsistent

@[simp] lemma IsModifier.one : γ.IsModifier 1 := .one'

set_option backward.isDefEq.respectTransparency false in
lemma isModifier_iff_ae_eq (hγ : γ.IsProper) :
    γ.IsModifier ρ ↔ (∀ Λ, Measurable (ρ Λ)) ∧ ∀ ⦃Λ₁ Λ₂⦄, Λ₁ ⊆ Λ₂ → ∀ η,
      ρ Λ₂ =ᵐ[γ Λ₂ η] fun η ↦ ∫⁻ ζ, ρ Λ₂ ζ ∂(γ Λ₁ η).withDensity (ρ Λ₁) := by
  simp only [isModifier_iff, IsConsistent, modificationKer, Kernel.ext_iff, Kernel.comp_apply,
    Kernel.coe_mk, Kernel.coe_comap, CompTriple.comp_eq, Measure.ext_iff, exists_prop,
    and_congr_right_iff]
  refine fun hρ ↦ forall₄_congr fun Λ₁ Λ₂ hΛ η ↦ ?_
  sorry

lemma isModifier_iff_ae_comm [DecidableEq S] :
    γ.IsModifier ρ ↔ (∀ Λ, Measurable (ρ Λ)) ∧
    ∀ ⦃Λ₁ Λ₂⦄, Λ₁ ⊆ Λ₂ → ∀ η₁, ∀ᵐ η₂ ∂γ (Λ₂ \ Λ₁) η₁, ∀ᵐ ζ ∂(γ Λ₁ η₂).prod (γ Λ₂ η₂),
      ρ Λ₂ ζ.1 * ρ Λ₁ ζ.2 = ρ Λ₂ ζ.2 * ρ Λ₁ ζ.1 := by
  -- simp only [isModifier_iff_ae_eq, and_congr_right_iff]
  -- refine fun hρ ↦ forall₄_congr fun Λ₁ Λ₂ hΛ η ↦ ?_
  sorry

/-- Modification specification.

Modifying the specification `γ` by a family indexed by finsets `Λ : Finset S` of densities
`ρ Λ : (S → E) → ℝ≥0∞` results in a family of kernels `γ.modificationKer ρ _ Λ` whose density is
that of `γ Λ` multiplied by `ρ Λ`.

When the family of densities `ρ` is a modifier (`Specification.IsModifier`), modifying a
specification results in a specification `γ.modification ρ _`. -/
noncomputable def modification (γ : Specification S E) (ρ : Finset S → (S → E) → ℝ≥0∞)
    (hρ : γ.IsModifier ρ) : Specification S E where
  toFun := modificationKer γ ρ hρ.measurable
  isConsistent' := hρ.isConsistent

-- This is not simp as we want to keep `modificationKer` an implementation detail
lemma coe_modification (γ : Specification S E) (ρ : Finset S → (S → E) → ℝ≥0∞)
    (hρ : γ.IsModifier ρ) : γ.modification ρ hρ = modificationKer γ ρ hρ.measurable := rfl

@[simp]
lemma modification_apply (γ : Specification S E) (ρ : Finset S → (S → E) → ℝ≥0∞)
    (hρ : γ.IsModifier ρ) (Λ : Finset S) (η : S → E) :
    γ.modification ρ hρ Λ η = (γ Λ η).withDensity (ρ Λ) := rfl

@[simp]
lemma modificationKer_modification {ρ₁ ρ₂ : Finset S → (S → E) → ℝ≥0∞}
    (hρ₁ : γ.IsModifier ρ₁) (hρ₂ : ∀ Λ, Measurable (ρ₂ Λ)) :
    modificationKer (γ.modification ρ₁ hρ₁) ρ₂ hρ₂ =
      modificationKer γ (ρ₁ * ρ₂) (fun Λ ↦ (hρ₁.measurable Λ).mul (hρ₂ Λ)) := by
  ext Λ η; simp [withDensity_mul, hρ₁.measurable, hρ₂]

@[simp] lemma IsModifier.mul {ρ₁ ρ₂ : Finset S → (S → E) → ℝ≥0∞}
    (hρ₁ : γ.IsModifier ρ₁) (hρ₂ : (γ.modification ρ₁ hρ₁).IsModifier ρ₂) :
    γ.IsModifier (ρ₁ * ρ₂) where
  measurable Λ := (hρ₁.measurable _).mul (hρ₂.measurable _)
  isConsistent := by simpa using hρ₂.isConsistent

@[simp] lemma modification_one' (γ : Specification S E) :
    γ.modification (fun _Λ _η ↦ 1) .one' = γ := by ext; simp

@[simp] lemma modification_one (γ : Specification S E) : γ.modification 1 .one = γ := by ext; simp

@[simp] lemma modification_modification (γ : Specification S E) (ρ₁ ρ₂ : Finset S → (S → E) → ℝ≥0∞)
    (hρ₁ : γ.IsModifier ρ₁) (hρ₂ : (γ.modification ρ₁ hρ₁).IsModifier ρ₂) :
    (γ.modification ρ₁ hρ₁).modification ρ₂ hρ₂ = γ.modification (ρ₁ * ρ₂) (hρ₁.mul hρ₂) := by
  ext Λ σ s hs
  simp only [modification_apply, Pi.mul_apply]
  rw [withDensity_apply _ hs, withDensity_apply _ hs,
    setLIntegral_withDensity_eq_setLIntegral_mul _ (hρ₁.measurable Λ) (hρ₂.1 Λ) hs]

protected lemma IsProper.modification (hγ : γ.IsProper) {hρ} : (γ.modification ρ hρ).IsProper := by
  refine IsProper.of_inter_eq_indicator_mul fun Λ A hA B hB η ↦ ?_
  rw [modification_apply, withDensity_apply _ hA,
    withDensity_apply _ (hA.inter <| cylinderEvents_le_pi _ hB),
    hγ.setLIntegral_inter_eq_indicator_mul_setLIntegral _ (hρ.measurable _) hA hB]

/-- A premodifier is a family indexed by finsets `Λ : Finset S` of densities
`ρ Λ : (S → E) → ℝ≥0∞` such that:
* each `ρ Λ` is measurable,
* `ρ Λ₂ ζ * ρ Λ₁ η = ρ Λ₁ ζ * ρ Λ₂ η` for all `Λ₁ Λ₂ : Finset S` and `ζ η : S → E` such that
  `Λ₁ ⊆ Λ₂` and `∀ (s : Λ₁ᶜ), ζ s = η s`. -/
structure IsPremodifier [MeasurableSpace E] (ρ : Finset S → (S → E) → ℝ≥0∞) : Prop where
  measurable Λ : Measurable (ρ Λ)
  comm_of_subset ⦃Λ₁ Λ₂ : Finset S⦄ ⦃ζ η : S → E⦄ (hΛ : Λ₁ ⊆ Λ₂)
    (hrestrict : ∀ s ∉ Λ₁, ζ s = η s) : ρ Λ₂ ζ * ρ Λ₁ η = ρ Λ₁ ζ * ρ Λ₂ η

lemma IsPremodifier.isModifier_div (hρ : IsPremodifier ρ) (ν : Measure E) [IsProbabilityMeasure ν] :
    (isssd ν).IsModifier fun Λ σ ↦ ρ Λ σ / ∫⁻ x, ρ Λ x ∂(isssd ν Λ σ) where
  measurable Λ :=
    (hρ.measurable Λ).div ((hρ.measurable Λ).lintegral_kernel.mono cylinderEvents_le_pi le_rfl)
  isConsistent Λ₁ Λ₂ hΛ := by
    sorry

end Modifier
end Specification
