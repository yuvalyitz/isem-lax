import Lax271696.GraphEncoding
import Lax470956.ParameterizedComplexity

/-!
---
title: Multicoloured Clique
type: definition
---
An instance is a graph on $n$ vertices together with a colouring of its vertices by $k$
colours, in which adjacent vertices always receive different colours. It is a
yes-instance if the graph contains a clique with one vertex of each colour — necessarily
of size $k$.

Parameterized by the number $k$ of colours, this problem is W[1]-complete. It is the
standard starting point for parameterized hardness proofs, because a reduction from it
may assume the $k$ vertices of a solution are distinguishable in advance, one per colour.

# Formalization notes

The graph is a mathlib `SimpleGraph (Fin n)` and is encoded by the compressed sparse row
format of `Lax271696.GraphEncoding`, so that an instance of this problem is an
instance of the format every other statement in the archive built on that encoding uses.
The colouring is appended as one entry per vertex, and the number of colours as a final
entry, following the convention that a parameterized instance carries its parameter at
the end of the word.

That adjacent vertices differ in colour is a field of the instance rather than a
consequence: the source of this problem is a $k$-partite graph with edges only between
distinct parts, and a reduction from it uses that the endpoints of an edge have two
different colours. It costs nothing, since an instance violating it has no multicoloured
clique through the offending edge anyway.

The adjacency list of each vertex is required to be strictly increasing. The archive's
graph format does not ask for this — it lets a list name its neighbours in any order and
more than once — but sorted lists are the convention of the format in practice, and
the requirement is what lets a linear-time reduction enumerate the edges in a canonical
order by a single scan. Without it a reduction would first have to sort and deduplicate
its input; that is possible in linear time, but it is work about the input format rather
than about the problem, and restricting the admissible words only makes the source
problem easier to be reduced *from* in the sense that fewer words need handling — the
problem itself, a graph and a colouring, is unchanged.

A solution is given as a function from colours to vertices rather than as a set, so that
"one vertex of each colour" is the statement that the function is a section of the
colouring, and the size of the clique needs no separate cardinality argument.
-/

namespace Lax470956.MulticolouredClique

/-- An instance of Multicoloured Clique: a graph whose vertices are coloured so that
adjacent vertices differ in colour. -/
structure Instance where
  /-- The number `k` of colours, the parameter. -/
  colours : ℕ
  /-- The number `n` of vertices. -/
  vertices : ℕ
  /-- The graph. -/
  graph : SimpleGraph (Fin vertices)
  /-- The colour of each vertex. -/
  colour : Fin vertices → Fin colours
  /-- Adjacent vertices differ in colour. -/
  adj_colour_ne : ∀ u v, graph.Adj u v → colour u ≠ colour v

/-- `G` contains a multicoloured clique: one vertex of each colour, pairwise adjacent. -/
def Instance.HasMulticolouredClique (G : Instance) : Prop :=
  ∃ f : Fin G.colours → Fin G.vertices,
    (∀ c, G.colour (f c) = c) ∧ ∀ c c', c ≠ c' → G.graph.Adj (f c) (f c')

/-- The word `x` presents the instance `G`: a compressed sparse row block encoding the
graph, with each adjacency list strictly increasing, followed by one entry per vertex
giving its colour, followed by the number of colours. -/
def EncodesInstance (x : List ℕ) (G : Instance) : Prop :=
  ∃ g, x = g ++ (List.ofFn fun v => (G.colour v : ℕ)) ++ [G.colours] ∧
    Lax271696.GraphEncoding.EncodesGraph g G.vertices G.graph ∧
    ∀ u < G.vertices, ∀ t, Lax271696.GraphEncoding.offset g u ≤ t →
      t + 1 < Lax271696.GraphEncoding.offset g (u + 1) →
      Lax271696.GraphEncoding.target g t < Lax271696.GraphEncoding.target g (t + 1)

/-- The words that encode an instance. -/
def Instances : Set (List ℕ) := {x | ∃ G, EncodesInstance x G}

/-- **Multicoloured Clique**, parameterized by the number of colours. The parameter is
the last entry of the word. -/
def problem : ParameterizedComplexity.Problem where
  Domain := Instances
  Yes x := ∃ G, EncodesInstance x G ∧ G.HasMulticolouredClique
  param x := x.getLast? |>.getD 0

end Lax470956.MulticolouredClique
