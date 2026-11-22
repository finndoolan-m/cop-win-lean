/-
Copyright 2026 The Formal Conjectures Authors.

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

public import Mathlib

/-!
# Dismantlable graphs are cop-win, and trees have cop number 1

Formal Conjectures' statement `MeynielConjecture.meyniel_conjecture.variants.tree`, copied from
`FormalConjectures/Wikipedia/MeynielConjecture.lean` at commit
`2207c54d0dbe960de591d280f997b195bf3f6e28`, with its `category` and `AMS` attributes removed and
`Mathlib` imported in place of Formal Conjectures' library. The definitions `Step`,
`CopsCatchWithin`, `CopsWin` and `copNumber` are copied with their bodies unchanged.

*Reference:* Nowakowski, R. and Winkler, P. (1983). "Vertex-to-vertex pursuit in a graph."
*Discrete Math.* 43, pp. 235--239.
-/

@[expose] public section

namespace MeynielConjecture

variable {V : Type*}

/-- A **move** in the cops-and-robbers game: stay put, or slide along an edge. -/
def Step (G : SimpleGraph V) (u v : V) : Prop :=
  u = v ∨ G.Adj u v

/-- `CopsCatchWithin G k m c r`: with `k` cops at positions `c`, the robber at `r`, and the cops
to move, the cops can guarantee to catch the robber within `m` further rounds. In each round
every cop moves (or stays), catching the robber if a cop reaches the robber's vertex, and then
the robber moves (or stays). -/
def CopsCatchWithin (G : SimpleGraph V) (k : ℕ) : ℕ → (Fin k → V) → V → Prop
  | 0, c, r => ∃ i, c i = r
  | m + 1, c, r =>
      (∃ i, c i = r) ∨
        ∃ c' : Fin k → V, (∀ i, Step G (c i) (c' i)) ∧
          ((∃ i, c' i = r) ∨ ∀ r', Step G r r' → CopsCatchWithin G k m c' r')

/-- `k` cops have a winning strategy on `G`: they can choose starting positions such that,
wherever the robber starts, they catch the robber in finitely many rounds. -/
def CopsWin (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ c : Fin k → V, ∀ r : V, ∃ m, CopsCatchWithin G k m c r

/-- The **cop number** `c(G)`: the least number of cops that can guarantee to catch the
robber on `G`. -/
noncomputable def copNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | CopsWin G k}

/--
**Trees are cop-win (Nowakowski–Winkler 1983).**

Every nonempty tree has cop number `1`: a single cop, always moving towards the robber, catches
the robber on any connected acyclic graph. More generally, the cop-win graphs are exactly the
dismantlable graphs.

*Reference:* [NW83].
-/
theorem meyniel_conjecture.variants.tree {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (hc : G.Connected) (ha : G.IsAcyclic) :
    copNumber G = 1 := by
  sorry

end MeynielConjecture

/-!
# Cop-win graphs are exactly the dismantlable graphs (Nowakowski–Winkler 1983)

The main result of this project: a finite graph is cop-win if and only if it is
dismantlable. A vertex `u` of `S` is a **corner**, covered by `w ≠ u`, when
every vertex of `S` that `u` can step to, `w` can step to as well (`N[u] ⊆ N[w]` inside `S`). A
set is **dismantlable** when corners can be deleted one at a time until a single vertex is left.
`IsCorner` and `Dismantlable` are copied unchanged from `CopWin/Dismantlable.lean`.

*Reference:* Nowakowski, R. and Winkler, P. (1983). "Vertex-to-vertex pursuit in a graph."
*Discrete Math.* 43, pp. 235--239.
-/

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

/-- **Nowakowski–Winkler.** A dismantlable finite graph has cop number `1`. -/
theorem Dismantlable.copNumber_eq_one [Fintype V] [Nonempty V]
    (h : Dismantlable G Set.univ) : copNumber G = 1 := by
  sorry

/-- **Nowakowski–Winkler.** A finite nonempty graph has cop number `1` if and only if it is
dismantlable. -/
theorem copNumber_eq_one_iff_dismantlable [Fintype V] [Nonempty V] :
    copNumber G = 1 ↔ Dismantlable G Set.univ := by
  sorry

end CopWin
