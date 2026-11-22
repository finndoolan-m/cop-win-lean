/-
Copyright 2026 Finn Doolan.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import CopWin.Game

/-!
# Shadow maps

A **shadow map** from `S` onto a smaller set `T` is a map `f` that

* sends `S` into `T`,
* turns legal moves into legal moves, and
* lets a cop on `f x` reach every vertex the robber on `x` can step to.

The theorem `ShadowMap.copWinOn`: if one cop wins on `T`, then one cop wins on `S`. The cop plays
its winning strategy on `T` against the robber's shadow `f r`. Once it catches the shadow, it is
one step from the robber, wherever the robber goes next.
-/

@[expose] public section

namespace CopWin

open MeynielConjecture

variable {V : Type*} {G : SimpleGraph V}

/-- `f` is a shadow map from `S` onto `T ⊆ S`. -/
structure ShadowMap (G : SimpleGraph V) (S T : Set V) (f : V → V) : Prop where
  subset : T ⊆ S
  mapsTo : ∀ x ∈ S, f x ∈ T
  step : ∀ x ∈ S, ∀ y ∈ S, Step G x y → Step G (f x) (f y)
  cover : ∀ x ∈ S, ∀ y ∈ S, Step G x y → Step G (f x) y

namespace ShadowMap

variable {S T : Set V} {f : V → V}

/-- Catching the shadow within `m` rounds on `T` means catching the robber within `m + 1` rounds
on `S`. -/
theorem catch_succ_of_shadow (hf : ShadowMap G S T f) {m : ℕ} {c r : V} (hr : r ∈ S)
    (h : Catch G T m c (f r)) : Catch G S (m + 1) c r := by
  induction m generalizing c r with
  | zero =>
    rw [catch_zero] at h
    exact catch_succ_of_step hr (h ▸ hf.cover r hr r hr (step_refl r))
  | succ m ih =>
    rcases catch_succ.mp h with h | ⟨c', hc', hcc', h | h⟩
    · exact catch_succ_of_step hr (h ▸ hf.cover r hr r hr (step_refl r))
    · -- The cop lands on the shadow: next round it steps onto the robber.
      exact catch_succ.mpr <| Or.inr ⟨c', hf.subset hc', hcc', Or.inr fun r' hr' hrr' =>
        catch_succ_of_step hr' (h ▸ hf.cover r hr r' hr' hrr')⟩
    · -- The robber moves to `r'`, so its shadow moves to `f r'`.
      exact catch_succ.mpr <| Or.inr ⟨c', hf.subset hc', hcc', Or.inr fun r' hr' hrr' =>
        ih hr' (h (f r') (hf.mapsTo r' hr') (hf.step r hr r' hr' hrr'))⟩

/-- **Shadow strategy.** If one cop wins on `T`, it wins on `S`. -/
theorem copWinOn (hf : ShadowMap G S T f) (hT : CopWinOn G T) : CopWinOn G S := by
  obtain ⟨c, hc, h⟩ := hT
  refine ⟨c, hf.subset hc, fun r hr => ?_⟩
  obtain ⟨m, hm⟩ := h (f r) (hf.mapsTo r hr)
  exact ⟨m + 1, hf.catch_succ_of_shadow hr hm⟩

end ShadowMap

end CopWin
