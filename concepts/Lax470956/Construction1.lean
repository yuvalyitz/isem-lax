import Lax470956.MulticolouredClique
import Lax470956.Scheduling
import Lax470956.InstanceEncoding
import Mathlib.Data.Nat.Choose.Basic

/-!
---
title: Construction 1
type: definition
---
The scheduling instance built from a Multicoloured Clique instance. There is one
*edge selection machine* for each of the $\binom{k}{2}$ pairs of colours and one
*validation machine*, so the number of machines depends on the number of colours alone
— so the reduction is a parameterized one.

Vertices are laid out along the time axis in an order $\pi$ that refines the colour
order, each vertex owning a window of length $k+2$. A vertex $v$ contributes one job of
processing time $k+2$ for its own colour, eligible only on the validation machine, and
one unit job for each other colour $\ell$, eligible also on the edge selection machine of
$\{\mathrm{colour}(v), \ell\}$. An edge $\{u,v\}$ with $\mathrm{colour}(u) <
\mathrm{colour}(v)$ contributes one job on the edge selection machine of that colour
pair, spanning from just after $u$'s window to just before $v$'s. Each colour pair also
gets two *colour combination* jobs per vertex, which fill the rest of that machine's
timeline so that exactly one edge job can be selected on it.

The weights are chosen in three tiers, $c_1 \ll c_2 \ll c_3$, so that a schedule of the
target weight is forced to select one edge per colour pair, and then forced to have those
$\binom{k}{2}$ edges agree on one vertex per colour — which is the clique.

# Formalization notes

The construction is a total function on Multicoloured Clique instances, so the map it
induces is defined everywhere and the statements about it need no side condition.

Jobs and machines are numbered rather than tagged, because an instance is something a
machine is handed and a word presents its jobs in an order. Machine $\binom{k}{2}$ is the
validation machine; the edge selection machine of the colour pair $\{a, b\}$ with $a < b$
is machine $b(b-1)/2 + a$, the position of $\{a,b\}$ in the enumeration of pairs by
larger element then smaller. That numbering is a bijection onto $\binom{k}{2}$, so the
machine count is exactly the paper's.

Jobs come in three blocks. Vertex job $vk + \ell$ is the job of vertex $v$ for colour
$\ell$. Then $k^2 n$ colour combination slots, slot $nk + (ak + b)n + z$ belonging to the
ordered colour pair $(a,b)$ and the vertex $z$. Then one slot per oriented edge.

The combination block is indexed by *all* ordered colour pairs, not only the admissible
ones, because a closed-form index is what a machine can compute: recovering $(a, b, z)$
from a slot is two divisions, whereas enumerating only the admissible pairs would require
a search. A slot whose pair is inadmissible — $a \ge b$, or $z$ coloured neither $a$ nor
$b$ — carries an *inert* job: weight zero and no eligible machine at all, so no feasible
schedule can place it and no schedule's weight can mention it. Inert jobs therefore
change neither side of the correctness statement, and there are only $k^2 n$ of them.

The edge block cannot be padded the same way. A slot for every pair of vertices would be
$n^2$ jobs, and the word the reduction reads has length $\Theta(n + m)$; a reduction
whose running time is linear in its input cannot write more than that, so a graph with
few edges would put the bound out of reach. The edges are therefore enumerated, and there
is exactly one slot per edge.

Two details are done slightly differently from the paper. The paper gives the edge job of
$\{u, v\}$, with $\mathrm{colour}(u) = \ell < \ell' = \mathrm{colour}(v)$, the processing
time $(k+2)(\pi(v) - \pi(u)) - \ell + \ell'$; here it is one unit shorter,
$(k+2)(\pi(v) - \pi(u)) - \ell + \ell' - 1$. With the paper's formula the edge job would
start one unit before the job $j_u^{(\ell')}$ ends and the two would conflict; with the
shorter one the five jobs that Lemma 1 places on an edge selection machine — the two colour
combination jobs, $j_u^{(\ell')}$, the edge job and $j_v^{(\ell)}$ — occupy consecutive
intervals, which is what the paper's Figure 1 shows, and Lemma 1's schedule is feasible.
Colours are numbered $0, \dots, k-1$ rather than $1, \dots, k$. With colours from $1$ the
colour combination job of the $\pi$-first vertex for the pair $(1, k)$ has processing
time $(k+2) \cdot 1 - k - 2 = 0$; from $0$ every processing time is positive. Neither
change affects the theorem: the weights, the machines and the argument are the paper's.

Processing times and deadlines are clamped, exactly as in Construction 2: the raw formulas
satisfy $0 < p \le d$ on every admissible slot, and the clamp is what discharges the two
standing conventions without a hypothesis on slots where they are not defined. On an
admissible slot the clamp is inactive.

The order $\pi$ is not a parameter but a definition: vertices are ranked by colour, ties
broken by index. The paper takes any order refining the colour order and the argument uses
nothing else about it; fixing one keeps the construction a function of its input alone.
-/

namespace Lax470956.Construction1

open Lax470956.MulticolouredClique

variable (G : MulticolouredClique.Instance)

/-- The number of vertices. -/
abbrev nVert : ℕ := G.vertices

/-- The number of colours, the parameter. -/
abbrev nCol : ℕ := G.colours

/-- The paper's order `<π`, as the position it assigns: vertices ranked by colour, ties
broken by index, counting from one. -/
noncomputable def rank (v : Fin G.vertices) : ℕ :=
  1 + (Finset.univ.filter fun u : Fin G.vertices =>
        (G.colour u : ℕ) < (G.colour v : ℕ) ∨
          ((G.colour u : ℕ) = (G.colour v : ℕ) ∧ (u : ℕ) < (v : ℕ))).card

/-- The window length `K = k + 2` each vertex occupies. -/
abbrev K : ℕ := G.colours + 2

/-- `c₁ = n + 1`: the weight of a vertex job for a colour other than its own. -/
def c1 : ℕ := G.vertices + 1

/-- `c₂ = (k-1)·n·c₁ + n + 1`: above the total weight of every vertex job together. -/
def c2 : ℕ := (G.colours - 1) * G.vertices * c1 G + G.vertices + 1

/-- `c₃ = (kn + k²n)·n·c₂ + 1`: above the total weight of every colour combination job
together. -/
def c3 : ℕ := (G.colours * G.vertices + G.colours ^ 2 * G.vertices) * G.vertices * c2 G + 1

/-- The machine of the colour pair `{a, b}` with `a < b`: its position `b(b-1)/2 + a` in
the enumeration of pairs by larger element, then smaller, written with the binomial
coefficient it is. -/
def pairIdx (a b : ℕ) : ℕ := b.choose 2 + a

/-- The validation machine. -/
abbrev validation : ℕ := G.colours.choose 2

/-- One machine per colour pair, plus the validation machine. -/
def nMach : ℕ := G.colours.choose 2 + 1

/-- The vertex jobs: one per vertex and colour. -/
abbrev nVJob : ℕ := G.vertices * G.colours

/-- The colour combination slots: one per ordered colour pair and vertex. -/
abbrev nCJob : ℕ := G.colours * G.colours * G.vertices

open Classical in
/-- The oriented edges of the graph, smaller colour first, in lexicographic order. This
is the enumeration the edge jobs are indexed by. There is one slot per edge and not one
per pair of vertices, because the word the reduction is handed lists the edges and a
reduction running in time linear in it cannot afford a slot for every pair. -/
noncomputable def edgeList : List (Fin G.vertices × Fin G.vertices) :=
  ((List.finRange G.vertices) ×ˢ (List.finRange G.vertices)).filter
    fun p => decide ((G.colour p.1 : ℕ) < (G.colour p.2 : ℕ) ∧ G.graph.Adj p.1 p.2)

/-- The edge slots: one per oriented edge. -/
noncomputable abbrev nEJob : ℕ := (edgeList G).length

/-- The jobs of the construction. -/
noncomputable def nJobs : ℕ := nVJob G + nCJob G + nEJob G

variable {G}

/-- The colour of vertex number `v`, as a number, and `0` when `v` is out of range. -/
noncomputable def col (v : ℕ) : ℕ :=
  if h : v < G.vertices then (G.colour ⟨v, h⟩ : ℕ) else 0

/-- The position of vertex number `v`, and `0` when `v` is out of range. -/
noncomputable def pos (v : ℕ) : ℕ :=
  if h : v < G.vertices then rank G ⟨v, h⟩ else 0

variable (G)

-- A job index below `n·k` is a vertex job; the next `k²n` are colour combination slots
-- and the rest, one per edge, are edge slots.

/-- The vertex of vertex job `j`. -/
def vjVert (j : ℕ) : ℕ := j / G.colours

/-- The colour of vertex job `j`. -/
def vjCol (j : ℕ) : ℕ := j % G.colours

/-- The smaller colour of colour combination slot `q`. -/
def cjA (q : ℕ) : ℕ := q / G.vertices / G.colours

/-- The larger colour of colour combination slot `q`. -/
def cjB (q : ℕ) : ℕ := q / G.vertices % G.colours

/-- The vertex of colour combination slot `q`. -/
def cjZ (q : ℕ) : ℕ := q % G.vertices

/-- The first endpoint of edge slot `q`. -/
noncomputable def ejU (q : ℕ) : ℕ := (((edgeList G)[q]?).map fun p => (p.1 : ℕ)).getD 0

/-- The second endpoint of edge slot `q`. -/
noncomputable def ejV (q : ℕ) : ℕ := (((edgeList G)[q]?).map fun p => (p.2 : ℕ)).getD 0

/-- A colour combination slot carries a job when its pair is ordered and its vertex has
one of the two colours. -/
def CJobOk (q : ℕ) : Prop :=
  cjA G q < cjB G q ∧ cjB G q < G.colours ∧ cjZ G q < G.vertices ∧
    (col (G := G) (cjZ G q) = cjA G q ∨ col (G := G) (cjZ G q) = cjB G q)

/-- An edge slot carries a job when it names one of the enumerated edges. Every slot of
the edge block does, so the block has no inert slots; the condition is here because the
accessors below are total functions on slot numbers. -/
noncomputable def EJobOk (q : ℕ) : Prop := q < (edgeList G).length

-- The raw formulas below are the paper's, with the edge job one unit shorter and colours
-- from zero, as the notes above say. An inert slot is given a unit job with no eligible
-- machine; on every admissible slot the clamp is inactive.

open Classical in
/-- The paper's processing time of job `j`, before clamping. -/
noncomputable def rawProc (j : ℕ) : ℕ :=
  if j < nVJob G then
    (if vjCol G j = col (G := G) (vjVert G j) then K G else 1)
  else if j < nVJob G + nCJob G then
    let q := j - nVJob G
    if CJobOk G q then
      (if col (G := G) (cjZ G q) = cjA G q
        then K G * pos (G := G) (cjZ G q) - cjB G q - 2
        else K G * (G.vertices - pos (G := G) (cjZ G q)) + cjA G q + 2)
    else 1
  else
    let q := j - nVJob G - nCJob G
    if EJobOk G q then
      K G * (pos (G := G) (ejV G q) - pos (G := G) (ejU G q))
        - col (G := G) (ejU G q) + col (G := G) (ejV G q) - 1
    else 1

open Classical in
/-- The paper's deadline of job `j`, before clamping. -/
noncomputable def rawDue (j : ℕ) : ℕ :=
  if j < nVJob G then
    (if vjCol G j = col (G := G) (vjVert G j)
      then K G * pos (G := G) (vjVert G j) + 1
      else K G * pos (G := G) (vjVert G j) - vjCol G j)
  else if j < nVJob G + nCJob G then
    let q := j - nVJob G
    if CJobOk G q then
      (if col (G := G) (cjZ G q) = cjA G q
        then K G * pos (G := G) (cjZ G q) - cjB G q - 1
        else K G * G.vertices + 2)
    else 1
  else
    let q := j - nVJob G - nCJob G
    if EJobOk G q then
      K G * pos (G := G) (ejV G q) - col (G := G) (ejU G q) - 1
    else 1

/-- The processing time of job `j`, clamped so that `0 < p ≤ d` holds outright. -/
noncomputable def procOf (j : ℕ) : ℕ := max 1 (min (rawProc G j) (rawDue G j))

/-- The deadline of job `j`, clamped so that `0 < p ≤ d` holds outright. -/
noncomputable def dueOf (j : ℕ) : ℕ := max 1 (rawDue G j)

open Classical in
/-- The weight of job `j`. An inert slot has weight zero. -/
noncomputable def wtOf (j : ℕ) : ℕ :=
  if j < nVJob G then
    (if vjCol G j = col (G := G) (vjVert G j) then 1 else c1 G)
  else if j < nVJob G + nCJob G then
    let q := j - nVJob G
    if CJobOk G q then
      (if col (G := G) (cjZ G q) = cjA G q
        then c2 G * pos (G := G) (cjZ G q)
        else c2 G * (G.vertices - pos (G := G) (cjZ G q)))
    else 0
  else
    let q := j - nVJob G - nCJob G
    if EJobOk G q then
      c2 G * (pos (G := G) (ejV G q) - pos (G := G) (ejU G q)) + c3 G
    else 0

open Classical in
/-- The machines eligible to run job `j`, as a list of machine numbers. An inert slot has
none, so no feasible schedule can place it. -/
noncomputable def eligOf (j : ℕ) : List ℕ :=
  if j < nVJob G then
    (if vjCol G j = col (G := G) (vjVert G j) then [validation G]
      else [validation G,
        pairIdx (min (vjCol G j) (col (G := G) (vjVert G j)))
                (max (vjCol G j) (col (G := G) (vjVert G j)))])
  else if j < nVJob G + nCJob G then
    let q := j - nVJob G
    if CJobOk G q then [pairIdx (cjA G q) (cjB G q)] else []
  else
    let q := j - nVJob G - nCJob G
    if EJobOk G q then
      [pairIdx (col (G := G) (ejU G q)) (col (G := G) (ejV G q))]
    else []

lemma procOf_pos (j : ℕ) : 0 < procOf G j := by
  simp only [procOf]; omega

lemma procOf_le_dueOf (j : ℕ) : procOf G j ≤ dueOf G j := by
  simp only [procOf, dueOf]; omega

open Classical in
/-- **Construction 1.** The scheduling instance built from the Multicoloured Clique
instance `G`. -/
noncomputable def inst : Scheduling.Instance where
  jobs := nJobs G
  machines := nMach G
  p j := procOf G j
  d j := dueOf G j
  w j := wtOf G j
  eligible j := Finset.univ.filter fun i : Fin (nMach G) => (i : ℕ) ∈ eligOf G j
  p_pos j := procOf_pos G j
  p_le_d j := procOf_le_dueOf G j

@[simp] lemma inst_jobs : (inst G).jobs = nJobs G := rfl
@[simp] lemma inst_machines : (inst G).machines = nMach G := rfl

/-- **The threshold `W` of Lemmas 1 and 2.** -/
def targetWeight : ℕ :=
  G.colours.choose 2 * c3 G + G.colours.choose 2 * (G.vertices * c2 G) +
    (G.colours - 1) * G.vertices * c1 G + G.colours

/-- Where job `j`'s block of eligible machines begins. -/
noncomputable def offOf (j : ℕ) : ℕ :=
  ((List.range j).map fun i => (eligOf G i).length).sum

/-- The processing-time block. -/
noncomputable def procBlock : List ℕ := (List.range (nJobs G)).map (procOf G)

/-- The deadline block. -/
noncomputable def dueBlock : List ℕ := (List.range (nJobs G)).map (dueOf G)

/-- The weight block. -/
noncomputable def wtBlock : List ℕ := (List.range (nJobs G)).map (wtOf G)

/-- The offset block, one entry per job and one more. -/
noncomputable def offBlock : List ℕ := (List.range (nJobs G + 1)).map (offOf G)

/-- The target block: the eligible machines of each job in turn. -/
noncomputable def tgtBlock : List ℕ := (List.range (nJobs G)).flatMap (eligOf G)

/-- **The word Construction 1 emits**: the instance, followed by the threshold. -/
noncomputable def emit : List ℕ :=
  ([nJobs G, nMach G] ++ procBlock G ++ dueBlock G ++ wtBlock G ++ offBlock G ++ tgtBlock G)
    ++ [targetWeight G]

/-- **The emitted word presents the constructed instance and its threshold.** -/
axiom emit_encodes (G : MulticolouredClique.Instance) :
    Lax470956.InstanceEncoding.EncodesDecisionInstance (emit G) (inst G) (targetWeight G)

/-- **The machine count.** The constructed instance has one machine per pair of colours
and one more, so its number of machines depends on the parameter alone. -/
axiom machines_eq (G : MulticolouredClique.Instance) : (inst G).machines = G.colours.choose 2 + 1

/-- **Construction 1 is correct.** The graph has a multicoloured clique exactly when the
constructed instance admits a feasible schedule of weight at least `W`. -/
axiom correct (G : MulticolouredClique.Instance) :
    G.HasMulticolouredClique ↔ (inst G).HasWeight (targetWeight G)

-- The construction as a map on words.

/-- The word a malformed input is sent to: one job of weight one, no machine to run it
on, and the threshold one. No schedule reaches the threshold, so the word is a
no-instance, as the source problem says of a word that is not a graph. -/
def noWord : List ℕ := [1, 0, 1, 1, 1, 0, 0, 1]

open Classical in
/-- **Construction 1 as a total map on words.** A word that does not encode a
Multicoloured Clique instance is sent to a fixed decision instance no schedule can
satisfy. A reduction is a function on all words, and the machine that computes it has to
decide which case it is in; making the diversion part of the map rather than a side
condition is what keeps the statements below free of hypotheses.

The case split is on a proposition rather than on a decision procedure, and the instance
the word is read as is chosen rather than computed, so the map is `noncomputable` in
Lean. Nothing is lost on either count: a word determines its instance up to everything
the construction looks at, so the correctness statement below does not mention the choice;
what has to be computable is the machine program. -/
noncomputable def reduce (x : List ℕ) : List ℕ :=
  if h : ∃ G, MulticolouredClique.EncodesInstance x G then emit h.choose else noWord

/-- **The reduction lands in the domain of the scheduling problem.** Every word it emits
presents an instance together with a threshold. -/
axiom reduce_maps (x : List ℕ) :
    reduce x ∈ Lax470956.InstanceEncoding.DecisionInstances

/-- **The reduction is correct.** A word encodes a graph with a multicoloured clique
exactly when the word it is sent to presents an instance meeting its threshold.

No well-formedness hypothesis is needed: a word that encodes no graph satisfies neither
side, the left because there is no graph to have a clique and the right because the word
it is sent to has a job it cannot run. -/
axiom reduce_correct (x : List ℕ) :
    (∃ G, MulticolouredClique.EncodesInstance x G ∧ G.HasMulticolouredClique) ↔
      ∃ I W, Lax470956.InstanceEncoding.EncodesDecisionInstance (reduce x) I W ∧
        I.HasWeight W

/-- **The reduction raises the parameter by a function of it alone.** The number of
machines of the image is $\binom{k}{2}+1$, where $k$ — the parameter of the source — is
the last entry of the word. This is the inequality that makes the reduction a
parameterized one rather than merely a correct one. -/
axiom reduce_param (x : List ℕ) :
    Lax470956.InstanceEncoding.machineCount (reduce x) ≤ (x.getLast?.getD 0).choose 2 + 1

end Lax470956.Construction1
