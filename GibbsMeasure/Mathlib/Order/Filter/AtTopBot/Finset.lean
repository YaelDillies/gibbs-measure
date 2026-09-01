/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Mathlib.Order.Filter.AtTopBot.Finset

/-!
# Countable generation of `atTop` on finite sets
-/

@[expose] public section

open Filter

variable {α : Type*}

instance Filter.isCountablyGenerated_atTop_finset [Countable α] :
    (atTop : Filter (Finset α)).IsCountablyGenerated := by
  rw [Filter.atTop_finset_eq_iInf]; infer_instance
