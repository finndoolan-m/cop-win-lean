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

import Solution

/-!
# Axioms of the main results

Fails if the main theorems come to depend on anything beyond Lean's three standard axioms
(in particular `sorryAx`, or `Lean.ofReduceBool` from `native_decide`).
-/

/--
info: 'MeynielConjecture.meyniel_conjecture.variants.tree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms MeynielConjecture.meyniel_conjecture.variants.tree

/--
info: 'CopWin.Dismantlable.copNumber_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CopWin.Dismantlable.copNumber_eq_one

/--
info: 'CopWin.copNumber_eq_one_iff_dismantlable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CopWin.copNumber_eq_one_iff_dismantlable
