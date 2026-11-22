# Dismantlable graphs are cop-win, in Lean 4

A Lean 4 proof of the Nowakowski–Winkler theorem: in the game of cops and robbers, one cop
can always catch the robber on a finite **dismantlable** graph. As a corollary, every finite
tree has cop number 1, which proves `meyniel_conjecture.variants.tree` from DeepMind's
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/Wikipedia/MeynielConjecture.lean`).

*Reference:* R. Nowakowski and P. Winkler, "Vertex-to-vertex pursuit in a graph",
*Discrete Math.* 43 (1983), 235–239.

## The idea

- A **corner** is a vertex `u` with another vertex `w` whose closed neighbourhood contains
  `u`'s: `N[u] ⊆ N[w]`.
- A graph is **dismantlable** if corners can be deleted one at a time until one vertex is left.
- **Shadow strategy:** the cop plays its winning strategy on the smaller graph against the
  robber's *shadow*, which is the robber, except that a robber on `u` counts as standing on `w`.
  Once the shadow is caught, the cop is one step from the robber.
- **Trees:** every leaf is a corner, covered by its neighbour.

## Files

- `Challenge.lean`: the statement, copied from Formal Conjectures at commit `245cf25a`.
- `Solution.lean`: the proof of that statement.
- `CopWin/Defs.lean`: the game definitions (`Step`, `CopsCatchWithin`, `CopsWin`,
  `copNumber`), copied unchanged from Formal Conjectures.
- `CopWin/Game.lean`: a one-cop game played inside a vertex set, and a bridge lemma showing it
  equals Formal Conjectures' game with one cop.
- `CopWin/Shadow.lean`: shadow maps; if one cop wins on the image, it wins on the whole set.
- `CopWin/Dismantlable.lean`: corners, dismantlability, and the Nowakowski–Winkler theorem.
- `CopWin/Tree.lean`: finite trees are dismantlable.
- `audit/Axioms.lean`: checks the proofs use only Lean's standard axioms (no `sorry`).

## Build

```bash
lake exe cache get
lake build
lake env lean audit/Axioms.lean
```

## Authorship and AI use

Work done by Finn Doolan, who chose the project and made the design decisions: a separate
one-cop game with a bridge lemma to Formal Conjectures' definition, a general shadow-map lemma
for the shadow strategy, and dismantlability as an inductive predicate on vertex sets. All Lean
code was drafted by Claude Code (Anthropic's AI coding tool) under Finn's direction. Lean checks
every proof.
