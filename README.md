# Cop-win graphs are exactly the dismantlable graphs, in Lean 4

To our knowledge, the first published Lean 4 proof of the Nowakowski–Winkler theorem: in the
game of cops and robbers, one cop can always catch the robber on a finite graph if and only if the
graph is dismantlable (`CopWin.copNumber_eq_one_iff_dismantlable`). As a corollary, every finite tree has cop number 1, proving `meyniel_conjecture.variants.tree` from
Google DeepMind's [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures)
([statement](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/MeynielConjecture.lean)).

*Reference:* R. Nowakowski and P. Winkler, "Vertex-to-vertex pursuit in a graph",
*Discrete Math.* 43 (1983), 235–239.
[doi:10.1016/0012-365X(83)90160-7](https://doi.org/10.1016/0012-365X(83)90160-7)

## Idea

- **Corner:** a vertex `u` with another vertex `w` whose closed neighbourhood contains `u`'s:
  `N[u] ⊆ N[w]`.
- **Dismantlable:** a graph is dismantlable if corners can be deleted one at a time until one
  vertex is left.
- **Strategy:** the cop plays its winning strategy on a smaller graph against the robber's
  *shadow*, which is the robber, except that a robber on `u` counts as standing on `w`. Once the
  shadow is caught, the cop is one step from the robber.
- **Converse:** follow the robber's longest escape. Just before capture, the robber is on some
  `u` and the cop on `w`, with every vertex the robber can reach also within the cop's reach, so `u`
  is a corner covered by `w`. Folding `u` onto `w` is a retract, and the cop keeps winning on the
  smaller graph by standing on the image of its old position. Induct.
- **Trees:** each leaf is a corner, covered by its neighbour.

## Files

- `Challenge.lean`: the statements checked by `comparator.json`: the Nowakowski–Winkler theorem
  (`CopWin.copNumber_eq_one_iff_dismantlable` and its forward direction), and the tree statement copied from Formal Conjectures
  at commit `2207c54d`.
- `Solution.lean`: the proofs of those statements.
- `CopWin/Defs.lean`: the game definitions (`Step`, `CopsCatchWithin`, `CopsWin`, `copNumber`),
  copied from Formal Conjectures.
- `CopWin/Game.lean`: a one-cop game played inside a vertex set, with a bridge lemma showing it
  equals Formal Conjectures' game with one cop.
- `CopWin/Shadow.lean`: shadow maps, with a lemma showing that if one cop wins on the smaller
  set, it wins on the whole set.
- `CopWin/Dismantlable.lean`: corners, dismantlability, and the Nowakowski–Winkler theorem.
- `CopWin/Converse.lean`: the converse (cop-win implies dismantlable) and the iff.
- `CopWin/Tree.lean`: a proof that finite trees are dismantlable.
- `audit/Axioms.lean`: a check that the proofs use only Lean's standard axioms (no `sorry`).

## Build

```bash
lake exe cache get
lake build
lake env lean audit/Axioms.lean
```

## Authorship

Work done by Finn Doolan, with LLM tools used for drafting code under his direction. All proofs are
checked by Lean.
