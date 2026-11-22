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

public import CopWin.Defs

/-!
# A one-cop game played inside a vertex set

`Catch G S m c r` is the one-cop version of Formal Conjectures' `CopsCatchWithin`, played on the
part of `G` inside `S`: the cop is a single vertex `c` rather than a map `Fin 1 → V`, and every
move must stay inside `S`. Playing inside `S` lets the proof shrink the board without changing
the vertex type.

The bridge `catch_univ_iff` shows that on `S = univ` this is exactly `CopsCatchWithin G 1`.
-/

@[expose] public section

namespace CopWin

open MeynielConjecture

variable {V : Type*} {G : SimpleGraph V}

lemma step_refl (u : V) : Step G u u := Or.inl rfl

lemma step_symm {u v : V} (h : Step G u v) : Step G v u := h.imp Eq.symm SimpleGraph.Adj.symm

/-- `Catch G S m c r`: with the cop on `c`, the robber on `r` and the cop to move, the cop can
guarantee to catch the robber within `m` rounds, where every move (cop or robber) stays in `S`. -/
def Catch (G : SimpleGraph V) (S : Set V) : ℕ → V → V → Prop
  | 0, c, r => c = r
  | m + 1, c, r =>
      c = r ∨ ∃ c' ∈ S, Step G c c' ∧ (c' = r ∨ ∀ r' ∈ S, Step G r r' → Catch G S m c' r')

/-- One cop wins on `S`: it can start somewhere in `S` and catch a robber starting anywhere
in `S`. -/
def CopWinOn (G : SimpleGraph V) (S : Set V) : Prop :=
  ∃ c ∈ S, ∀ r ∈ S, ∃ m, Catch G S m c r

lemma catch_zero {S : Set V} {c r : V} : Catch G S 0 c r ↔ c = r := Iff.rfl

lemma catch_succ {S : Set V} {m : ℕ} {c r : V} :
    Catch G S (m + 1) c r ↔
      c = r ∨ ∃ c' ∈ S, Step G c c' ∧ (c' = r ∨ ∀ r' ∈ S, Step G r r' → Catch G S m c' r') :=
  Iff.rfl

/-- A cop one step away from the robber catches it on its next move. -/
lemma catch_succ_of_step {S : Set V} {m : ℕ} {c r : V} (hr : r ∈ S) (h : Step G c r) :
    Catch G S (m + 1) c r :=
  catch_succ.mpr (Or.inr ⟨r, hr, h, Or.inl rfl⟩)

/-- **Bridge to Formal Conjectures.** On the whole graph, the one-cop game is the repo's game
with `k = 1`. -/
lemma catch_univ_iff {m : ℕ} {c r : V} :
    Catch G Set.univ m c r ↔ CopsCatchWithin G 1 m (fun _ => c) r := by
  induction m generalizing c r with
  | zero => exact ⟨fun h => ⟨0, h⟩, fun ⟨_, h⟩ => h⟩
  | succ m ih =>
    rw [catch_succ, CopsCatchWithin]
    constructor
    · rintro (h | ⟨c', -, hcc', h | h⟩)
      · exact Or.inl ⟨0, h⟩
      · exact Or.inr ⟨fun _ => c', fun _ => hcc', Or.inl ⟨0, h⟩⟩
      · exact Or.inr ⟨fun _ => c', fun _ => hcc', Or.inr fun r' hr' => ih.mp (h r' trivial hr')⟩
    · rintro (⟨_, h⟩ | ⟨c', hcc', ⟨i, h⟩ | h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨c' i, trivial, hcc' i, Or.inl h⟩
      · have hc' : c' = fun _ => c' 0 := funext fun i => congrArg c' (Subsingleton.elim i 0)
        refine Or.inr ⟨c' 0, trivial, hcc' 0, Or.inr fun r' _ hr' => ih.mpr ?_⟩
        rw [← hc']
        exact h r' hr'

lemma copsWin_one_of_copWinOn (h : CopWinOn G Set.univ) : CopsWin G 1 := by
  obtain ⟨c, -, hc⟩ := h
  exact ⟨fun _ => c, fun r => (hc r trivial).imp fun _ => catch_univ_iff.mp⟩

/-! The next three lemmas are the API lemmas of `MeynielConjecture.lean`, with their proofs copied
from there. -/

lemma not_copsCatchWithin_zero (m : ℕ) (c : Fin 0 → V) (r : V) :
    ¬CopsCatchWithin G 0 m c r := by
  induction m generalizing c r with
  | zero =>
    rintro ⟨i, -⟩
    exact i.elim0
  | succ m ih =>
    rintro (⟨i, -⟩ | ⟨c', -, ⟨i, -⟩ | h⟩)
    · exact i.elim0
    · exact i.elim0
    · exact ih c' r (h r (Or.inl rfl))

lemma not_copsWin_zero [Nonempty V] : ¬CopsWin G 0 := by
  rintro ⟨c, hc⟩
  obtain ⟨m, hm⟩ := hc (Classical.arbitrary V)
  exact not_copsCatchWithin_zero m c _ hm

lemma copsWin_card [Fintype V] : CopsWin G (Fintype.card V) :=
  ⟨(Fintype.equivFin V).symm, fun r => ⟨0, ⟨Fintype.equivFin V r, by simp⟩⟩⟩

/-- If one cop wins on the whole graph, the cop number is `1`. -/
theorem copNumber_eq_one_of_copWinOn [Fintype V] [Nonempty V] (h : CopWinOn G Set.univ) :
    copNumber G = 1 := by
  refine le_antisymm (Nat.sInf_le (copsWin_one_of_copWinOn h)) ?_
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  rcases Nat.sInf_eq_zero.mp h0 with h | h
  · exact not_copsWin_zero h
  · exact Set.eq_empty_iff_forall_notMem.mp h _ copsWin_card

end CopWin
