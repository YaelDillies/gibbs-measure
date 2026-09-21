/-
Copyright (c) 2026 Yaël Dillies, Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Matteo Cipollina
-/
module

public import Mathlib.Logic.Equiv.List
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Mathlib.Order.Filter.AtTopBot.Finset
public import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# Summation along the powerset net

`SummationFilter.powerset ι` sums a family indexed by `Finset ι` along the net of partial sums
over `{A | A ⊆ s}` as `s : Finset ι` ranges over `atTop`. This is coarser than unconditional
summation.
-/

@[expose] public section

open Filter

namespace SummationFilter

variable (ι : Type*)

/-- Partial sums over the subsets of a finite set, as that set ranges over `atTop`. -/
def powerset : SummationFilter (Finset ι) := ⟨Filter.map Finset.powerset atTop⟩

variable {ι}

lemma powerset_filter : (powerset ι).filter = Filter.map Finset.powerset atTop := rfl

instance : (powerset ι).LeAtTop := ⟨Filter.tendsto_finset_powerset_atTop_atTop⟩

instance : (powerset ι).NeBot := ⟨Filter.map_neBot⟩

instance [Countable ι] : (powerset ι).filter.IsCountablyGenerated := by
  rw [powerset_filter]
  infer_instance

end SummationFilter

namespace HasSum

variable {ι α : Type*} [AddCommMonoid α] [TopologicalSpace α] {f : Finset ι → α} {a : α}

lemma powerset (h : HasSum f a) : HasSum f a (SummationFilter.powerset ι) :=
  h.mono_left (SummationFilter.le_atTop (L := SummationFilter.powerset ι))

lemma powerset_iff :
    HasSum f a (SummationFilter.powerset ι) ↔
      Tendsto (fun s : Finset ι ↦ ∑ i ∈ s.powerset, f i) atTop (nhds a) := by
  rw [HasSum, SummationFilter.powerset_filter, tendsto_map'_iff, Function.comp_def]

end HasSum

namespace Summable

variable {ι α : Type*} [AddCommMonoid α] [TopologicalSpace α] {f : Finset ι → α}

lemma powerset (h : Summable f) : Summable f (SummationFilter.powerset ι) :=
  h.mono_filter (SummationFilter.le_atTop (L := SummationFilter.powerset ι))

end Summable
