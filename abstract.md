Interval scheduling with eligible machine sets asks for a maximum-weight feasible schedule
of $n$ interval jobs on $m$ parallel machines, where each job has a weight, a processing
time and a deadline, and may only be run by the machines in its own eligible set.
Hermelin, Itzhaki, Molter and Shabtay (2024) study its parameterized complexity for the
number of machines $m$ and the maximum processing time $p_{\max}$. This submission
formalizes their three results.

**Theorem 1.** Parameterized by $m$, the problem is W[1]-hard: Multicoloured Clique,
parameterized by the number of colours, fpt-reduces to it. Multicoloured Clique is
W[1]-complete (Fellows, Hermelin, Rosamond and Vialette 2009), so this is W[1]-hardness;
the class W[1] itself is not formalized, and the statement is the reduction. An instance
with $k$ colours becomes an instance on $\binom{k}{2}+1$ machines. The construction
follows the paper, with two details done slightly differently: the processing time of an
edge job is one unit shorter, and colours are numbered from zero.

**Theorem 2.** The problem is NP-hard even when every processing time is at most $25$ and
every weight is $1$, and so para-NP-hard for $p_{\max}$. The reduction starts from
$(3,4)$-satisfiability — three literals per clause, at most four occurrences of each
variable — whose NP-hardness (Tovey 1984) is the one result taken as given and left
unproven in this submission.

**Theorem 3.** For the combined parameter $m + p_{\max}$ the problem is fixed-parameter
tractable: a dynamic program over machine occupancy, run on the word RAM, decides it
within $c\,(m\,p_{\max}+1)^{2m}\,(m+1)\,(|x|+1)$ instructions, and the result is also
stated in the qualitative form FPT. Together with the first two theorems, the combined
parameter is tractable and neither half of it is.

Running times are stated on the word RAM of the archive, against an explicit word encoding
of an instance, so that the claims are about the instructions a machine executes rather
than about an annotation on a function. NP-hardness quantifies over NP as usual.
