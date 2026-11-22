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

public import CopWin.Dismantlable

/-!
# Finite trees are dismantlable

A leaf `v` of a tree, with unique neighbour `w`, is a corner covered by `w`. Deleting the leaf
leaves a smaller tree, so by induction on the number of vertices every finite tree is
dismantlable, and so has cop number `1`.

Mathlib deletes the leaf by passing to the induced graph on the subtype `{v}ᶜ`. The lemma
`Dismantlable.image_val` carries dismantlability on that subtype back to the set `{v}ᶜ` of the
original graph.
-/

@[expose] public section

namespace CopWin

open MeynielConjecture

variable {V : Type*} {G : SimpleGraph V}

lemma step_induce_iff {s : Set V} {a b : s} : Step (G.induce s) a b ↔ Step G a b := by
  simp [Step, Subtype.ext_iff]

/-- Dismantlability on an induced subgraph carries over to the original graph. -/
lemma Dismantlable.image_val {s : Set V} {T : Set s} (h : Dismantlable (G.induce s) T) :
    Dismantlable G (Subtype.val '' T) := by
  induction h with
  | single v =>
    rw [Set.image_singleton]
    exact Dismantlable.single _
  | @corner T u w hc _ ih =>
    obtain ⟨hu, hw, huw, hcov⟩ := hc
    refine Dismantlable.corner (u := u) (w := w)
      ⟨⟨u, hu, rfl⟩, ⟨w, hw, rfl⟩, Subtype.val_injective.ne huw, ?_⟩ ?_
    · rintro _ ⟨x, hx, rfl⟩ hux
      exact step_induce_iff.mp (hcov x hx (step_induce_iff.mpr hux))
    · rwa [Set.image_sdiff Subtype.val_injective, Set.image_singleton] at ih

/-- A leaf of a tree is a corner, covered by its neighbour. -/
lemma isCorner_of_leaf {v w : V} (hvw : G.Adj v w) (huniq : ∀ x, G.Adj v x → x = w) :
    IsCorner G Set.univ v w := by
  refine ⟨trivial, trivial, hvw.ne, fun x _ hvx => ?_⟩
  rcases hvx with rfl | hvx
  · exact Or.inr hvw.symm
  · exact Or.inl (huniq x hvx).symm

/-- **Every finite tree is dismantlable.** -/
theorem IsTree.dismantlable {W : Type*} [Finite W] {H : SimpleGraph W} (hH : H.IsTree) :
    Dismantlable H Set.univ := by
  refine Finite.induction_subsingleton_or_nontrivial
    (P := fun W => ∀ H : SimpleGraph W, H.IsTree → Dismantlable H Set.univ) W ?_ ?_ H hH
  · intro W _ _ H hH
    obtain ⟨v⟩ := hH.connected.nonempty
    rw [show (Set.univ : Set W) = {v} from
      Set.eq_singleton_iff_unique_mem.mpr ⟨trivial, fun x _ => Subsingleton.elim x v⟩]
    exact Dismantlable.single v
  · intro W _ _ ih H hH
    classical
    have := Fintype.ofFinite W
    obtain ⟨v, hv⟩ := hH.exists_vert_degree_one_of_nontrivial
    obtain ⟨w, hvw, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
    have hT : (H.induce ({v}ᶜ : Set W)).IsTree :=
      ⟨hH.connected.induce_compl_singleton_of_degree_eq_one hv, hH.isAcyclic.induce _⟩
    have hlt : Nat.card ({v}ᶜ : Set W) < Nat.card W :=
      Finite.card_subtype_lt (p := (· ∈ ({v}ᶜ : Set W))) (x := v) (by simp)
    have hrest := (ih _ hlt _ hT).image_val
    rw [Set.image_univ, Subtype.range_coe, Set.compl_eq_univ_sdiff] at hrest
    exact Dismantlable.corner (isCorner_of_leaf hvw huniq) hrest

/-- **Trees are cop-win.** A finite nonempty connected acyclic graph has cop number `1`. -/
theorem copNumber_eq_one_of_isTree [Fintype V] [Nonempty V] (hc : G.Connected)
    (ha : G.IsAcyclic) : copNumber G = 1 :=
  (IsTree.dismantlable ⟨hc, ha⟩).copNumber_eq_one

end CopWin
