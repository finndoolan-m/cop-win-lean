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

public import CopWin.Shadow

/-!
# Dismantlable graphs are cop-win (Nowakowski–Winkler 1983)

A vertex `u` of `S` is a **corner**, covered by `w`, when every vertex of `S` that `u` can step
to, `w` can step to as well (`N[u] ⊆ N[w]` inside `S`). A set is **dismantlable** when corners
can be deleted one at a time until a single vertex is left.

Folding a corner `u` onto `w` is a shadow map from `S` onto `S \ {u}`, so by induction one cop
wins on every dismantlable set.

*Reference:* Nowakowski, R. and Winkler, P. (1983). "Vertex-to-vertex pursuit in a graph."
*Discrete Math.* 43, pp. 235--239.
-/

@[expose] public section

namespace CopWin

open MeynielConjecture

variable {V : Type*} {G : SimpleGraph V}

/-- `u` is a corner of `S`, covered by `w ≠ u`. -/
def IsCorner (G : SimpleGraph V) (S : Set V) (u w : V) : Prop :=
  u ∈ S ∧ w ∈ S ∧ u ≠ w ∧ ∀ x ∈ S, Step G u x → Step G w x

/-- `S` is dismantlable: it is a single vertex, or it has a corner `u` and `S \ {u}` is
dismantlable. -/
inductive Dismantlable (G : SimpleGraph V) : Set V → Prop
  | single (v : V) : Dismantlable G {v}
  | corner {S : Set V} {u w : V} :
      IsCorner G S u w → Dismantlable G (S \ {u}) → Dismantlable G S

/-- Fold `u` onto `w`, leaving every other vertex where it is. -/
def fold [DecidableEq V] (u w x : V) : V := if x = u then w else x

/-- Folding a corner onto the vertex that covers it is a shadow map. -/
theorem IsCorner.shadowMap [DecidableEq V] {S : Set V} {u w : V} (h : IsCorner G S u w) :
    ShadowMap G S (S \ {u}) (fold u w) := by
  obtain ⟨-, hw, huw, hcov⟩ := h
  refine ⟨Set.sdiff_subset, fun x hx => ?_, fun x hx y hy hxy => ?_, fun x hx y hy hxy => ?_⟩
  · unfold fold
    split_ifs with hxu
    · exact ⟨hw, fun h => huw (Set.mem_singleton_iff.mp h).symm⟩
    · exact ⟨hx, hxu⟩
  · unfold fold
    split_ifs with hxu hyu hyu
    · exact step_refl w
    · exact hcov y hy (hxu ▸ hxy)
    · subst hyu
      exact step_symm (hcov x hx (step_symm hxy))
    · exact hxy
  · unfold fold
    split_ifs with hxu
    · exact hcov y hy (hxu ▸ hxy)
    · exact hxy

lemma copWinOn_singleton (v : V) : CopWinOn G {v} :=
  ⟨v, rfl, fun _ hr => ⟨0, (Set.mem_singleton_iff.mp hr).symm⟩⟩

/-- **Nowakowski–Winkler.** One cop wins on every dismantlable set. -/
theorem Dismantlable.copWinOn {S : Set V} (h : Dismantlable G S) : CopWinOn G S := by
  induction h with
  | single v => exact copWinOn_singleton v
  | corner hc _ ih =>
    classical
    exact hc.shadowMap.copWinOn ih

/-- **Nowakowski–Winkler.** A dismantlable finite graph has cop number `1`. -/
theorem Dismantlable.copNumber_eq_one [Fintype V] [Nonempty V]
    (h : Dismantlable G Set.univ) : copNumber G = 1 :=
  copNumber_eq_one_of_copWinOn h.copWinOn

end CopWin
