import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# The finite model property for Henson graphs

The countable homogeneous graph omitting an r-clique is axiomatized by
clique-freeness and its one-vertex extension axioms. A finite fragment of
those axioms bounds the number of prescribed neighbors and nonneighbors.
A new vertex can have the required neighbors precisely when they contain
no clique of size r−1.

Sources
* https://en.wikipedia.org/wiki/Henson_graph
* Gregory Cherlin, Two problems on homogeneous structures, revisited, §11.1.
  https://janos.cs.technion.ac.il/RESEARCH/AMS-Book-files/pdfs/09_Cherlin.pdf

Credit: @dwilfand-sys
-/

namespace OMA.S_wp_do_the_henson_graphs_have_the_finite_model_property

/-- For each forbidden clique size and each finite extension bound, there
is a finite clique-free graph realizing every permitted adjacency pattern. -/
theorem main :
    ∀ r : ℕ, 3 ≤ r → ∀ k : ℕ, ∃ N : ℕ, ∃ G : SimpleGraph (Fin N),
      G.CliqueFree r ∧ ∀ A B : Finset (Fin N), Disjoint A B →
        (A ∪ B).card ≤ k → G.CliqueFreeOn (A : Set (Fin N)) (r - 1) →
        ∃ v : Fin N, v ∉ A ∪ B ∧
          (∀ a ∈ A, G.Adj v a) ∧ (∀ b ∈ B, ¬ G.Adj v b) := by
  sorry

end OMA.S_wp_do_the_henson_graphs_have_the_finite_model_property
