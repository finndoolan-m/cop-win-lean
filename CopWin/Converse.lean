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
# Cop-win graphs are dismantlable (Nowakowski–Winkler 1983, converse)

* **A corner from the last move.** If the cop wins from a position where it is not next to the
  robber, follow the robber's longest escape. Just before the cop catches it, the robber stands on
  some `u` with the cop on `w ≠ u`, and every vertex the robber can step to, the cop can step to:
  `u` is a corner covered by `w`. If the cop's start is next to every vertex, every other vertex is
  a corner covered by it.
* **Retracts keep cop-win.** Folding the corner `u` onto `w` retracts `S` onto `S \ {u}`. The cop
  plays its winning strategy on `S` and stands on the image of where that strategy puts it.
* **Induction** on the number of vertices then gives dismantlability.

*Reference:* Nowakowski, R. and Winkler, P. (1983). "Vertex-to-vertex pursuit in a graph."
*Discrete Math.* 43, pp. 235--239.
-/

@[expose] public section

namespace CopWin

open MeynielConjecture

variable {V : Type*} {G : SimpleGraph V}

/-- **Retracts keep cop-win.** If `f` retracts `S` onto `T` and preserves moves, a cop that
catches the robber within `m` rounds on `S` catches it within `m` rounds on `T` by standing on the
image of its position. -/
theorem catch_retract {S T : Set V} {f : V → V} (hTS : T ⊆ S) (hmap : ∀ x ∈ S, f x ∈ T)
    (hid : ∀ x ∈ T, f x = x) (hstep : ∀ x ∈ S, ∀ y ∈ S, Step G x y → Step G (f x) (f y))
    {m : ℕ} {c r : V} (hc : c ∈ S) (hr : r ∈ T) (h : Catch G S m c r) :
    Catch G T m (f c) r := by
  induction m generalizing c r with
  | zero =>
    rw [catch_zero] at h ⊢
    rw [h, hid r hr]
  | succ m ih =>
    rcases catch_succ.mp h with h | ⟨c', hc', hcc', h | h⟩
    · exact catch_succ.mpr (Or.inl (by rw [h, hid r hr]))
    · exact catch_succ.mpr <| Or.inr
        ⟨f c', hmap c' hc', hstep c hc c' hc' hcc', Or.inl (by rw [h, hid r hr])⟩
    · exact catch_succ.mpr <| Or.inr ⟨f c', hmap c' hc', hstep c hc c' hc' hcc',
        Or.inr fun r' hr' hrr' => ih hc' hr' (h r' (hTS hr') hrr')⟩

/-- Deleting a corner keeps cop-win. -/
theorem IsCorner.copWinOn_diff {S : Set V} {u w : V} (hc : IsCorner G S u w)
    (h : CopWinOn G S) : CopWinOn G (S \ {u}) := by
  classical
  have hf := hc.shadowMap
  have hid : ∀ x ∈ S \ {u}, fold u w x = x := fun x hx =>
    ite_eq_right_iff.mpr fun hxu => absurd (Set.mem_singleton_iff.mpr hxu) hx.2
  obtain ⟨c, hcS, hwin⟩ := h
  refine ⟨fold u w c, hf.mapsTo c hcS, fun r hr => ?_⟩
  obtain ⟨m, hm⟩ := hwin r (hf.subset hr)
  exact ⟨m, catch_retract hf.subset hf.mapsTo hid hf.step hcS hr hm⟩

/-- **A corner from the last move.** If the cop wins from a position where it is not next to the
robber, the set has a corner. -/
theorem exists_isCorner_of_catch {S : Set V} {m : ℕ} {c r : V} (hc : c ∈ S) (hr : r ∈ S)
    (hns : ¬Step G c r) (h : Catch G S m c r) : ∃ u w, IsCorner G S u w := by
  induction m generalizing c r with
  | zero =>
    rw [catch_zero] at h
    exact absurd (h ▸ step_refl c) hns
  | succ m ih =>
    rcases catch_succ.mp h with h | ⟨c', hc', hcc', h | h⟩
    · exact absurd (h ▸ step_refl c) hns
    · exact absurd (h ▸ hcc') hns
    · by_cases hall : ∀ r' ∈ S, Step G r r' → Step G c' r'
      · refine ⟨r, c', hr, hc', fun hrc => hns ?_, hall⟩
        rw [hrc]
        exact hcc'
      · push Not at hall
        obtain ⟨r', hr', hrr', hns'⟩ := hall
        exact ih hc' hr' hns' (h r' hr' hrr')

/-- **Nowakowski–Winkler, converse.** One cop wins on a finite set only if it is dismantlable. -/
theorem CopWinOn.dismantlable {S : Set V} (hS : S.Finite) (h : CopWinOn G S) :
    Dismantlable G S := by
  suffices key : ∀ n : ℕ, ∀ S : Set V, S.Finite → S.ncard ≤ n → CopWinOn G S → Dismantlable G S
    from key _ S hS le_rfl h
  intro n
  induction n with
  | zero =>
    intro S hS hn h
    obtain ⟨c, hc, -⟩ := h
    have : S = ∅ := (Set.ncard_eq_zero hS).mp (Nat.le_zero.mp hn)
    exact absurd (this ▸ hc) (Set.notMem_empty c)
  | succ n ih =>
    intro S hS hn h
    obtain ⟨c, hc, hwin⟩ := h
    by_cases hsub : S ⊆ {c}
    · rw [Set.Subset.antisymm hsub (Set.singleton_subset_iff.mpr hc)]
      exact Dismantlable.single c
    obtain ⟨u, w, huw⟩ : ∃ u w, IsCorner G S u w := by
      by_cases hfar : ∃ r ∈ S, ¬Step G c r
      · obtain ⟨r, hr, hns⟩ := hfar
        obtain ⟨m, hm⟩ := hwin r hr
        exact exists_isCorner_of_catch hc hr hns hm
      · push Not at hfar
        obtain ⟨u, hu, hne⟩ := Set.not_subset.mp hsub
        exact ⟨u, c, hu, hc, fun e => hne (Set.mem_singleton_iff.mpr e), fun x hx _ => hfar x hx⟩
    refine Dismantlable.corner huw (ih _ (hS.subset Set.sdiff_subset) ?_
      (huw.copWinOn_diff ⟨c, hc, hwin⟩))
    exact Nat.lt_succ_iff.mp ((Set.ncard_sdiff_singleton_lt_of_mem huw.1 hS).trans_le hn)

/-- If the cop number is `1`, one cop wins on the whole graph. -/
lemma copWinOn_univ_of_copNumber_eq_one [Fintype V] (h : copNumber G = 1) :
    CopWinOn G Set.univ := by
  have hmem : sInf {k | CopsWin G k} ∈ {k | CopsWin G k} := Nat.sInf_mem ⟨_, copsWin_card⟩
  have h1 : CopsWin G 1 := by
    have : sInf {k | CopsWin G k} = 1 := h
    rw [this] at hmem
    exact hmem
  obtain ⟨c, hc⟩ := h1
  have hconst : c = fun _ => c 0 := funext fun i => congrArg c (Subsingleton.elim i 0)
  refine ⟨c 0, trivial, fun r _ => (hc r).imp fun m hm => catch_univ_iff.mpr ?_⟩
  rw [← hconst]
  exact hm

/-- **Nowakowski–Winkler.** A finite nonempty graph has cop number `1` if and only if it is
dismantlable. -/
theorem copNumber_eq_one_iff_dismantlable [Fintype V] [Nonempty V] :
    copNumber G = 1 ↔ Dismantlable G Set.univ :=
  ⟨fun h => (copWinOn_univ_of_copNumber_eq_one h).dismantlable Set.finite_univ,
    Dismantlable.copNumber_eq_one⟩

end CopWin
