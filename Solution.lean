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

public import CopWin

/-!
# Trees have cop number 1: the statement of `Challenge.lean`, proved

The theorem follows from `CopWin.copNumber_eq_one_of_isTree` in `CopWin/Tree.lean`, which uses the
Nowakowski–Winkler theorem `CopWin.Dismantlable.copNumber_eq_one`.
-/

@[expose] public section

namespace MeynielConjecture

/--
**Trees are cop-win (Nowakowski–Winkler 1983).**

Every nonempty tree has cop number `1`: a single cop, always moving towards the robber, catches
the robber on any connected acyclic graph. More generally, the cop-win graphs are exactly the
dismantlable graphs.

*Reference:* [NW83].
-/
theorem meyniel_conjecture.variants.tree {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (hc : G.Connected) (ha : G.IsAcyclic) :
    copNumber G = 1 :=
  CopWin.copNumber_eq_one_of_isTree hc ha

end MeynielConjecture
