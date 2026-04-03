module

public import GibbsMeasure.Mathlib.MeasureTheory.Constructions.Cylinders
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
  coe_injective' γ₁ γ₂ h := by cases γ₁; cases γ₂; congr

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
variable (ν : Measure E) (η : S → E)

-- TODO: Use `measurable_of_measurable_coe'` + measurable rectangles here
set_option backward.isDefEq.respectTransparency false in
lemma measurable_isssdFun (Λ : Finset S) :
    Measurable[cylinderEvents Λᶜ]
      fun η : S → E ↦ (Measure.pi fun _ : Λ ↦ ν).map (juxt Λ η) := by
  refine @Measure.measurable_of_measurable_coe _ _ _ (_) _ ?_
  rw [MeasurableSpace.pi_eq_generateFrom_projections]
  refine @MeasurableSpace.generateFrom_induction _ _ _ ?_ ?_ ?_ ?_
  · rintro _ ⟨s, A, hA, rfl⟩ _
    have hA' : MeasurableSet (Function.eval s ⁻¹' A : Set (S → E)) := measurable_pi_apply s hA
    have come_on η := Measure.map_apply (α := ((Λ : Set S)) → E) (β := S → E)
      (f := juxt (Λ : Set S) η) (μ := Measure.pi fun _ : Λ ↦ ν) Measurable.juxt hA'
    stop
    simp only [come_on, ← preimage_comp]
    by_cases hs : s ∈ Λ
    · simp [Function.comp_def, juxt_apply_of_mem (Finset.mem_coe.2 hs)]
    · classical
      simp only [Function.comp_def, Finset.coe_sort_coe,
        juxt_apply_of_not_mem (Finset.mem_coe.not.2 hs), preimage_const, apply_ite, measure_empty]
      refine measurable_const.ite ?_ measurable_const
      sorry
  · simp
  · rintro A hA
    sorry
  · sorry

/-- Auxiliary definition for `Specification.isssd`. -/
@[simps -fullyApplied]
def isssdFun (ν : Measure E) (Λ : Finset S) : Kernel[cylinderEvents Λᶜ] (S → E) (S → E) :=
  @Kernel.mk _ _ (_) _
    (fun η ↦ Measure.map (juxt Λ η) (Measure.pi fun _ : Λ ↦ ν))
    (measurable_isssdFun ν Λ)

/-- The ISSSD of a measure is strongly consistent. -/
lemma isssdFun_comp_isssdFun [DecidableEq S] (Λ₁ Λ₂ : Finset S) :
    (isssdFun ν Λ₁).comap id cylinderEvents_le_pi ∘ₖ isssdFun ν Λ₂ =
      (isssdFun ν (Λ₁ ∪ Λ₂)).comap id
        (measurable_id'' <| by gcongr; exact Finset.subset_union_right) :=
  sorry

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
        (measurable_id'' <| by gcongr; exact Finset.subset_union_right) := isssdFun_comp_isssdFun ..

protected lemma IsProper.isssd : (isssd (S := S) ν).IsProper := by
  refine .of_inter_eq_indicator_mul fun Λ A hA B hB x ↦ ?_
  simp only [isssd_apply, isssdFun_apply, Finset.coe_sort_coe]
  rw [Measure.map_apply .juxt (hA.inter (cylinderEvents_le_pi _ hB)), Measure.map_apply .juxt hA,
    Set.preimage_inter]
  by_cases hx : x ∈ B
  · have : juxt (↑Λ) x ⁻¹' B = Set.univ := by
      ext ζ
      simp only [mem_preimage, mem_univ, iff_true]
      exact (mem_congr_of_measurableSet_cylinderEvents hB
        fun _ hi ↦ juxt_apply_of_not_mem hi ζ).mpr hx
    rw [this, inter_univ, indicator_of_mem hx, Pi.one_apply, one_mul]
  · have : juxt (↑Λ) x ⁻¹' B = ∅ := by
      ext ζ
      simp only [mem_preimage, mem_empty_iff_false, iff_false]
      exact fun h ↦ hx ((mem_congr_of_measurableSet_cylinderEvents hB
        fun _ hi ↦ juxt_apply_of_not_mem hi ζ).mp h)
    rw [this, inter_empty, measure_empty, indicator_of_notMem hx, zero_mul]

instance isssd.instIsMarkov [IsProbabilityMeasure ν] : (isssd (S := S) ν).IsMarkov where
  isMarkovKernel Λ := ⟨fun _ ↦ by
    simp only [isssd_apply]
    exact Measure.isProbabilityMeasure_map Measurable.juxt.aemeasurable⟩

end ISSSD

section ProductMeasure

/-- The product measure `ν ^ S` is a `isssd μ`-Gibbs measure. -/
lemma isGibbsMeasure_isssd_infinitePi (ν : Measure E) [IsProbabilityMeasure ν] :
    (isssd ν).IsGibbsMeasure (.infinitePi fun _ : S ↦  ν) := by
  rintro Λ
  sorry

end ProductMeasure

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
