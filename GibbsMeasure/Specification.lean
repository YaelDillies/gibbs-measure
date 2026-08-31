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
  ∀ ⦃Λ₁ Λ₂⦄, Λ₁ ⊆ Λ₂ → (γ Λ₁).comap id (by exact cylinderEvents_le_pi) ∘ₖ γ Λ₂ = γ Λ₂

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
  ∀ ⦃Λ₁ Λ₂⦄ [DecidableEq S], (γ Λ₁).comap id (by exact cylinderEvents_le_pi) ∘ₖ γ Λ₂ =
      (γ (Λ₁ ∪ Λ₂)).comap id (by gcongr; exact Finset.subset_union_right)

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
variable {ν : Measure E} [IsProbabilityMeasure ν]

lemma measurable_isssdFun (Λ : Finset S) :
    Measurable[cylinderEvents Λᶜ]
      fun η : S → E ↦ (Measure.pi fun _ : Λ ↦ ν).map (juxt Λ η) := by
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    generateFrom_measurableSquareCylinders.symm IsPiSystem.measurableSquareCylinders ?_
  rintro A ⟨s, t, ht, rfl⟩
  exact measurable_map_juxt_pi (Measure.pi fun _ : Λ ↦ ν)
    (fun i ↦ ht i (mem_univ _)) s.countable_toSet

/-- Auxiliary definition for `Specification.isssd`. -/
@[simps -fullyApplied]
def isssdFun (ν : Measure E) [IsProbabilityMeasure ν] (Λ : Finset S) :
    Kernel[cylinderEvents Λᶜ] (S → E) (S → E) :=
  @Kernel.mk _ _ (_) _
    (fun η ↦ Measure.map (juxt Λ η) (Measure.pi fun _ : Λ ↦ ν))
    (measurable_isssdFun (ν := ν) Λ)

instance instIsMarkovKernel_isssdFun {Λ : Finset S} : IsMarkovKernel (isssdFun ν Λ) :=
  ⟨fun _ ↦ by simp only [isssdFun_apply]; infer_instance⟩

lemma isssdFun_pi [DecidableEq S] (Λ s : Finset S) (t : S → Set E)
    (ht : ∀ i, MeasurableSet (t i)) (η : S → E) :
    isssdFun ν Λ η ((s : Set S).pi t) =
      (((s \ Λ : Finset S) : Set S).pi t).indicator (fun _ ↦ ∏ i ∈ s ∩ Λ, ν (t i)) η := by
  have hprod :
      (Measure.pi fun _ : Λ ↦ ν)
        (univ.pi fun j : Λ ↦ if (j : S) ∈ s then t j else univ) =
      ∏ i ∈ s ∩ Λ, ν (t i) := by
    rw [Measure.pi_pi]
    simp only [apply_ite, measure_univ]
    exact (Finset.prod_attach Λ fun i : S ↦ if i ∈ s then ν (t i) else 1).trans <| by
      simp [Finset.prod_ite_mem, Finset.inter_comm]
  rw [isssdFun_apply, map_juxt_pi _ ht s.countable_toSet η]
  simp [Finset.coe_sdiff, hprod]

lemma lintegral_isssdFun_pi [DecidableEq S] {μ : Measure (S → E)}
    (Λ s : Finset S) (t : S → Set E) (ht : ∀ i, MeasurableSet (t i)) :
    ∫⁻ ω, isssdFun ν Λ ω ((s : Set S).pi t) ∂μ =
      (∏ i ∈ s ∩ Λ, ν (t i)) * μ (((s \ Λ : Finset S) : Set S).pi t) := by
  simp_rw [isssdFun_pi Λ s t ht]
  exact lintegral_indicator_const (MeasurableSet.pi (s \ Λ).countable_toSet fun i _ ↦ ht i) _

/-- Resampling `Λ₁` then `Λ₂` is resampling `Λ₁ ∪ Λ₂`. -/
lemma isssdFun_comp_isssdFun [DecidableEq S] (Λ₁ Λ₂ : Finset S) :
    (isssdFun ν Λ₁).comap id (by exact cylinderEvents_le_pi) ∘ₖ isssdFun ν Λ₂ =
      (isssdFun ν (Λ₁ ∪ Λ₂)).comap id (by gcongr; exact Finset.subset_union_right) := by
  refine DFunLike.ext _ _ fun η ↦ ext_of_generateFrom_of_isProbabilityMeasure
    generateFrom_measurableSquareCylinders.symm IsPiSystem.measurableSquareCylinders ?_
  rintro A ⟨s, t, ht, rfl⟩
  have ht' (i) : MeasurableSet (t i) := ht i (mem_univ _)
  rw [Kernel.comp_apply, Measure.bind_apply
    (MeasurableSet.pi s.countable_toSet fun i _ ↦ ht' i) (Kernel.aemeasurable _)]
  simp_rw [Kernel.comap_apply, id_eq]
  rw [lintegral_isssdFun_pi Λ₁ s t ht',
    isssdFun_pi Λ₂ (s \ Λ₁) t ht' η,
    isssdFun_pi (Λ₁ ∪ Λ₂) s t ht' η, ← indicator_const_mul]
  congr 1
  · ext; simp
  ext
  rw [← Finset.prod_inter_mul_prod_sdiff (s ∩ (Λ₁ ∪ Λ₂)) Λ₁ fun i ↦ ν (t i)]
  congr 1
  · rw [Finset.inter_assoc, Finset.inter_eq_right.2 Finset.subset_union_left]
  · rw [Finset.inter_sdiff_assoc, Finset.union_sdiff_left, Finset.inter_comm,
      Finset.inter_sdiff_left_comm]

/-- The **Independent Specification with Single Spin Distribution**.

This is the specification corresponding to the product measure. -/
@[simps]
def isssd (ν : Measure E) [IsProbabilityMeasure ν] : Specification S E where
  toFun := isssdFun ν
  isConsistent' Λ₁ Λ₂ hΛ := by
    classical
    rw [isssdFun_comp_isssdFun]
    ext a s _
    simp only [Kernel.comap_apply, id_eq, isssdFun_apply, Finset.coe_sort_coe]
    rw [Finset.union_eq_right.2 hΛ]

protected lemma IsIndep.isssd : (isssd (S := S) ν).IsIndep :=
  fun _ _ ↦ isssdFun_comp_isssdFun ..

protected lemma IsProper.isssd : (isssd (S := S) ν).IsProper :=
  .of_inter_eq_indicator_mul fun Λ A hA B hB x ↦ by
    simp only [isssd_apply, isssdFun_apply, Finset.coe_sort_coe]
    rw [Measure.map_apply .juxt (hA.inter (cylinderEvents_le_pi _ hB)), Measure.map_apply .juxt hA,
      preimage_inter]
    have hxB (ζ) : juxt (↑Λ) x ζ ∈ B ↔ x ∈ B :=
      mem_congr_of_measurableSet_cylinderEvents hB fun _ hi ↦ juxt_apply_of_not_mem hi ζ
    by_cases hx : x ∈ B
    · have : juxt (↑Λ) x ⁻¹' B = univ := by ext; simp [hxB, hx]
      rw [this, inter_univ, indicator_of_mem hx, Pi.one_apply, one_mul]
    · have : juxt (↑Λ) x ⁻¹' B = ∅ := by ext; simp [hxB, hx]
      rw [this, inter_empty, measure_empty, indicator_of_notMem hx, zero_mul]

instance isssd.instIsMarkov : (isssd (S := S) ν).IsMarkov where
  isMarkovKernel Λ := ⟨inferInstanceAs <|
    ∀ η, IsProbabilityMeasure (.map (juxt (Λ : Set S) η) <| .pi fun _ ↦ ν)⟩

section ProductMeasure

lemma isssd_pi {Λ s : Finset S} (hs : s ⊆ Λ) (t : S → Set E)
    (ht : ∀ i, MeasurableSet (t i)) (η : S → E) :
    isssd ν Λ η ((s : Set S).pi t) = ∏ i ∈ s, ν (t i) := by
  classical
  rw [isssd_apply, isssdFun_pi Λ s t ht,
    Finset.sdiff_eq_empty_iff_subset.2 hs]
  simp [Finset.inter_eq_left.2 hs]

lemma bind_isssd_pi (μ : Measure (S → E)) {Λ s : Finset S}
    (hs : s ⊆ Λ) (t : S → Set E) (ht : ∀ i, MeasurableSet (t i)) :
    μ.bind (isssd ν Λ) ((s : Set S).pi t) = μ univ * ∏ i ∈ s, ν (t i) := by
  rw [Measure.bind_apply (MeasurableSet.pi s.countable_toSet fun i _ ↦ ht i)
    ((isssd ν Λ).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable]
  simp_rw [isssd_pi hs t ht]
  rw [lintegral_const, mul_comm]

lemma infinitePi_bind_isssd (Λ : Finset S) :
    (Measure.infinitePi fun _ : S ↦ ν).bind (isssd ν Λ) =
      Measure.infinitePi fun _ : S ↦ ν := by
  classical
  refine Measure.eq_infinitePi (μ := fun _ : S ↦ ν) fun s t ht ↦ ?_
  rw [Measure.bind_apply (MeasurableSet.pi s.countable_toSet fun i _ ↦ ht i)
    ((isssd ν Λ).measurable.mono cylinderEvents_le_pi le_rfl).aemeasurable, isssd_apply,
    lintegral_isssdFun_pi Λ s t ht,
    Measure.infinitePi_pi (μ := fun _ : S ↦ ν) fun i _ ↦ ht i]
  exact Finset.prod_inter_mul_prod_sdiff s Λ fun i ↦ ν (t i)

/-- The product measure `ν ^ S` is a `isssd ν`-Gibbs measure. -/
lemma isGibbsMeasure_isssd_infinitePi :
    (isssd ν).IsGibbsMeasure (.infinitePi fun _ : S ↦ ν) :=
  (isGibbsMeasure_iff_forall_bind_eq IsProper.isssd).2 infinitePi_bind_isssd

lemma isGibbsMeasure_isssd_iff (μ : Measure (S → E)) [IsProbabilityMeasure μ] :
    (isssd ν).IsGibbsMeasure μ ↔ μ = Measure.infinitePi fun _ : S ↦ ν := by
  refine ⟨fun hμ ↦ Measure.eq_infinitePi (μ := fun _ : S ↦ ν) fun s t ht ↦ ?_,
    fun h ↦ h ▸ isGibbsMeasure_isssd_infinitePi⟩
  rw [← (isGibbsMeasure_iff_forall_bind_eq IsProper.isssd).1 hμ s,
    bind_isssd_pi μ le_rfl t ht, measure_univ, one_mul]

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

@[simp]
lemma modification_one' (γ : Specification S E) :
    γ.modification (fun _Λ _η ↦ 1) .one' = γ := by ext; simp

@[simp]
lemma modification_one (γ : Specification S E) : γ.modification 1 .one = γ := by ext; simp

@[simp]
lemma modification_modification (γ : Specification S E) (ρ₁ ρ₂ : Finset S → (S → E) → ℝ≥0∞)
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
