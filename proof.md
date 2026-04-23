# Key-centric BCNF decomposition

## Motivation

The textbook presentation of BCNF decomposition is **FD-centric**:
look for a nontrivial FD $X \to Y$ with a non-superkey LHS, split on
it, recurse. This forces the student to enumerate FDs (including
derived ones from $F^+$), it lets extraneous attributes sneak into
the LHS and inflate the split (producing redundancy), and for general
$F$ the BCNF check in principle requires iterating over every possible
LHS.

This note argues for a cleaner framing: **key-centric**.

Every BCNF violation is really a *missing key*. It is a set of
attributes $X$ that (i) determines something non-trivially, but
(ii) is not already a superkey. The decomposition step is not about
the FD; it is about $X$. Splitting $R$ into $R_1 = X^+$ and
$R_2 = (\mathcal{U} \setminus X^+) \cup X$ *promotes $X$ to a key* of
$R_1$ — that's the whole point of the decomposition. BCNF just means
"there is nothing left to promote."

So the algorithm reads:

> Find a set of attributes that could be made a key. Make it a key
> by decomposition. Repeat.

The two cases below — singleton $F$ and general $F$ — are the same
algorithm, instantiated at the right granularity.

## Setup

- $R$ is a relation with attribute set $\mathcal{U}$.
- $F$ is a set of FDs.
- $X^+$ is the attribute closure of $X \subseteq \mathcal{U}$ under $F$.
- For $S \subseteq \mathcal{U}$, the closure of $X \subseteq S$ *inside*
  $S$ is $X^+ \cap S$ (the standard identity
  $X^+_{\pi_S(F^+)} = X^+ \cap S$).
- $X$ is a **superkey of $S$** iff $X^+ \supseteq S$.
- An FD $X \to Y$ on $S$ is **nontrivial** iff $Y \not\subseteq X$,
  and **violates BCNF on $S$** iff it is nontrivial and $X$ is not a
  superkey of $S$.

## Key candidates

**Definition.** A set $X \subseteq S$ is a **key candidate of $S$**
iff
$$
X \;\subsetneq\; X^+ \cap S \;\subsetneq\; S.
$$
Equivalently, $X$ determines something in $S$ beyond itself
(so there *is* a nontrivial FD $X \to (X^+ \cap S) \setminus X$
inside $S$) yet $X$ is not already a superkey of $S$.

**BCNF as the absence of key candidates.**
$$
S \text{ is in BCNF} \;\Longleftrightarrow\; S \text{ has no key candidate.}
$$

*Proof.* ($\Rightarrow$) If $X$ is a key candidate, then $X \to (X^+ \cap S) \setminus X$
is a nontrivial FD on $S$ with non-superkey LHS, violating BCNF.
($\Leftarrow$) Any nontrivial $X \to Y$ violating BCNF on $S$ has $Y \not\subseteq X$,
so $X^+ \cap S \supsetneq X$, and $X$ not a superkey gives
$X^+ \cap S \subsetneq S$. So $X$ is a key candidate. $\blacksquare$

**The decomposition step.** Given a key candidate $X$ of $S$, split:
$$
S_1 \;=\; X^+ \cap S, \qquad S_2 \;=\; (S \setminus X^+) \cup X.
$$
By construction $X$ is a superkey of $S_1$ (it determines all of $S_1$),
so $X$ has been "promoted to a key" in $S_1$. Both halves contain $X$
and share only $X$: $S_1 \cap S_2 = X$.

Everything else is a question of *which* key candidate to pick.

## Singleton case

Assume $F$ consists of FDs $A \to B$ with $A, B \in \mathcal{U}$ and
$A \neq B$, and let $G_F$ be the directed graph with an edge $A \to B$
for each FD. Write $\mathrm{reach}(A)$ for the set of nodes reachable
from $A$ in $G_F$ (including $A$).

**Lemma 1 (Closure is reachability).** For singleton $F$,
$$
X^+ \;=\; \bigcup_{A \in X} \mathrm{reach}(A).
$$

*Proof.* Compute $X^+$ stepwise: $X_0 = X$, and
$X_{i+1} = X_i \cup \{C : \exists A \in X_i, A \to C \in F\}$.
Because every FD has a singleton LHS, the firing condition is "some
single attribute already in $X_i$".

(⊇) For $A \in X$ and $B \in \mathrm{reach}(A)$, follow the path
$A = A_0 \to A_1 \to \cdots \to A_k = B$: each edge $A_i \to A_{i+1}$
puts $A_{i+1}$ into $X_{i+1}$, so $B \in X^+$.

(⊆) Induct on the smallest $i$ with $B \in X_i$: either $B \in X$ (empty
path) or $B$ is added via $A \to B \in F$ with $A \in X_{i-1}$, and the
inductive hypothesis extends a path from $X$ to $A$ into one to $B$. $\blacksquare$

### Single-attribute key candidates suffice

For singleton $F$, a key candidate can always be taken to be a single
attribute. Concretely, $S$ has a key candidate iff it has a
single-attribute one:

**Theorem.** For singleton $F$ and any $S \subseteq \mathcal{U}$,
$$
S \text{ is in BCNF} \;\Longleftrightarrow\;
\forall A \in S,\; \mathrm{reach}(A) \cap S \in \{\{A\}, S\}.
$$
I.e., each attribute either reaches nothing new inside $S$, or is a
superkey of $S$ — never in between.

*Proof.* Going from key candidates to single attributes: if
$X \subseteq S$ is a key candidate, pick any $B \in (X^+ \cap S) \setminus X$.
By Lemma 1, $B$ is reachable from some $A_0 \in X$; since $B \neq A_0$
and $B \in S$, we have $\mathrm{reach}(A_0) \cap S \ni B \neq A_0$, so
it is not $\{A_0\}$. If it equaled $S$, then $A_0 \in X$ would make $X$
a superkey, contradicting the key-candidate property. So $A_0$ is a
*single-attribute* key candidate of $S$.

Going the other way: a single-attribute key candidate is a key
candidate. Applying the BCNF criterion above completes the
equivalence. $\blacksquare$

So for singleton $F$, the algorithm specializes to:

1. For each $A \in S$ that is an LHS of some FD in $F$ (others have
   $\mathrm{reach}(A) = \{A\}$ and pass trivially), check whether
   $\mathrm{reach}(A) \cap S = S$.
2. If every such $A$ is a superkey of $S$, $S$ is in BCNF — done.
3. Otherwise pick any violating $A$ and split on $\{A\}$:
   $$S_1 = \mathrm{reach}(A) \cap S, \qquad S_2 = (S \setminus \mathrm{reach}(A)) \cup \{A\}.$$
   $A$ is now a key of $S_1$. Recurse.

The whole procedure reads the graph $G_F$ once. No powerset, no
acyclicity required, no projection of FDs between steps.

### Uniqueness when $G_F$ is a forest

BCNF decomposition is famously non-unique: different choices of
violating FD can yield different final sets of sub-relations. The
smallest example is a **diamond**:
$A \to B,\ A \to C,\ B \to D,\ C \to D$. Splitting on $B$ yields
$\{B, D\}, \{A, B, C\}$; splitting on $C$ yields
$\{C, D\}, \{A, B, C\}$ — genuinely different.

Acyclicity alone is not enough (the diamond is acyclic). What fails
is a stronger tree-like property: $D$ has two parents, so sibling
subtrees are not disjoint. Requiring every node to have **in-degree
at most one** — i.e., $G_F$ is a forest — rules exactly this out.

Call $v$ **internal** if it has an outgoing edge in $G_F$ (i.e., $v$
is the LHS of some FD), and define $T_v = \{v\} \cup \mathrm{children}(v)$.
Let $K$ be the set of attributes with no incoming edge (roots of
each tree, plus isolated nodes) — the unique candidate key of $R$.

**Theorem (Uniqueness).** If $G_F$ is a forest, the decomposition is
uniquely determined and equals
$$
\mathcal{D} \;=\; \{T_v : v \text{ internal}\} \;\cup\; \{K\},
$$
with $K$ dropped when $|K| = 1$ (then $K \subseteq T_v$ for the unique
root $v$).

Uniqueness comes down to a one-step commutativity: if $A$ and $B$ are
both violating in $S$, processing them in either order yields the
same three pieces.

**Nested** ($B \in \mathrm{reach}(A)$, so $A$ is an ancestor of $B$).
Forest acyclicity gives $A \notin \mathrm{reach}(B)$; forest
in-degree $\le 1$ gives $\mathrm{reach}(B) \subseteq \mathrm{reach}(A)$.
Processing $A$ first then $B$ produces
$\mathrm{reach}(B) \cap S$, $(\mathrm{reach}(A) \cap S) \setminus \mathrm{reach}(B) \cup \{B\}$,
$(S \setminus \mathrm{reach}(A)) \cup \{A\}$. Processing $B$ first
then $A$ produces the same three sets by direct calculation (using
$\mathrm{reach}(B) \subseteq \mathrm{reach}(A)$ and $B \in \mathrm{reach}(A)$).

**Disjoint** ($A, B$ in different subtrees). This is where the
forest hypothesis earns its keep: sibling subtrees being disjoint
is exactly the in-degree-$\le 1$ property. Processing $A$ puts $B$
into the residue $S_2$, where $\mathrm{reach}(B) \cap S_2 = \mathrm{reach}(B) \cap S$
is unchanged and $B$ is still violating. Both orders yield
$\mathrm{reach}(A) \cap S$, $\mathrm{reach}(B) \cap S$,
$(S \setminus (\mathrm{reach}(A) \cup \mathrm{reach}(B))) \cup \{A, B\}$.

From the one-step commutativity, any two orderings can be bridged by
finitely many adjacent swaps; the final multiset of sub-relations is
an invariant of the algorithm. The characterization as
$\{T_v\} \cup \{K\}$ follows by induction on the number of internal
nodes.

**Why the diamond breaks this.** In the diamond, $B$ and $C$ are
siblings with a shared descendant $D$:
$\mathrm{reach}(B) \cap \mathrm{reach}(C) = \{D\}$ instead of empty.
Processing $B$ first puts $D$ into $\{B, D\}$ and removes it from the
residue; processing $C$ first puts $D$ into $\{C, D\}$. $D$ goes with
whichever parent is chosen first — exactly the ambiguity.

## General case

For arbitrary $F$, key candidates can be multi-attribute. The
algorithm iterates over them *in size order* and picks the first one
that works:

```
decompose(S):
  for k = 0, 1, 2, …, |S| − 1:
    for each X ⊆ S with |X| = k:
      if X ⊊ X⁺ ∩ S ⊊ S:                    # X is a key candidate of S
        return decompose(X⁺ ∩ S)
             ∪ decompose((S ∖ X⁺) ∪ X)
  return {S}
```

Call the first such $X$ encountered the **minimal key candidate** of
$S$. Its minimality has a useful form: every proper subset
$Y \subsetneq X$ has
$$
Y^+ \cap S \;=\; Y. \tag{$\star$}
$$
(A proper subset can't be a superkey — else $X$ would be too — and
by the "smallest first" rule it isn't a key candidate, so its closure
inside $S$ is itself.)

For singleton $F$, the minimal key candidate always has $|X| = 1$,
recovering the single-attribute algorithm above. The powerset loop is
the natural generalization when $F$ has multi-attribute LHSs.

### Non-redundancy

**Definition.** A decomposition $\mathcal{D} = \{S_1, \ldots, S_k\}$
is **non-redundant** if no member is contained in another: for all
$i \neq j$, $S_i \not\subseteq S_j$. The offending case is the
textbook example $F = \{Z \to W\}$ on $\mathcal{U} = \{X, Y, Z, W\}$,
where picking the augmented violating FD $\{Y, Z\} \to W$ (with
extraneous $Y$) produces
$\{\{X, Y, Z\}, \{Y, Z\}, \{Z, W\}\}$ and
$\{Y, Z\} \subsetneq \{X, Y, Z\}$.

**Theorem (Non-redundancy).** For any $F$, the powerset algorithm
produces a non-redundant decomposition.

*Proof.* Fix a split step: current sub-relation $S$, minimal key
candidate $X$, halves $S_1 = X^+ \cap S$ and
$S_2 = (S \setminus X^+) \cup X$. Two elementary facts:

- $S_1 \cap S_2 = X$ (direct calculation).
- $|S_1| \ge |X| + 1$ and $|S_2| \ge |X| + 1$, since
  $X \subsetneq X^+ \cap S \subsetneq S$.

**Key lemma.** Every key candidate $Y$ used inside the recursion on
$S_1$ or $S_2$ satisfies $Y \not\subseteq X$.

*Proof of lemma.* Let $T$ be a descendant piece ($T \subseteq S_1$
or $T \subseteq S_2$), and suppose $Y \subseteq X$.

- If $Y \subsetneq X$: by $(\star)$, $Y^+ \cap S = Y$. Since
  $T \subseteq S$, $Y^+ \cap T \subseteq Y^+ \cap S = Y$, so $Y^+ \cap T = Y$
  — $Y$ is trivially closed in $T$, not a key candidate.
- If $Y = X$ and $T \subseteq S_1 \subseteq X^+$: then $X^+ \cap T = T$,
  so $X$ is a superkey of $T$ — not a key candidate.
- If $Y = X$ and $T \subseteq S_2$: then
  $X^+ \cap T \subseteq X^+ \cap S_2 = X$; combined with $X \cap T \subseteq X^+ \cap T$,
  this gives $X^+ \cap T = X \cap T$, which is trivial (self-closed) —
  not a key candidate.

So no $Y \subseteq X$ is a key candidate in any $T$; every pivot used
inside the recursion has some attribute outside $X$. $\blacksquare$

**From the lemma to non-redundancy.** Both halves of any split
contain the pivot. The lemma says each recursion-pivot contributes
at least one attribute outside $X$ to both halves, so every piece
ever produced on the $S_1$-side contains an attribute of $X^+ \setminus X$,
and every piece on the $S_2$-side contains an attribute of
$S \setminus X^+$. In particular, any final sub-relation $L_1$
descending from $S_1$ has $L_1 \not\subseteq X$, and any $L_2$ from
$S_2$ has $L_2 \not\subseteq X$.

Let $L_1, L_2$ be two final sub-relations whose recursion paths
diverge at a split with pivot $X$, $L_1$ on the $S_1$-side and $L_2$
on the $S_2$-side. Then $L_1 \cap L_2 \subseteq S_1 \cap S_2 = X$, so
$L_1 \subseteq L_2$ would give $L_1 \subseteq X$, contradicting
$L_1 \not\subseteq X$. Symmetrically $L_2 \not\subseteq L_1$. Every
two final sub-relations are incomparable. $\blacksquare$

**Where the textbook algorithm goes wrong.** The textbook splits on
a violating FD $\alpha \to \beta$, and $\alpha$ may carry *extraneous*
attributes — attributes whose removal still leaves a valid (and still
violating) FD, like $Y$ in $\{Y, Z\} \to W$ when $Z \to W$ already
holds. The inflated $\alpha$ propagates into $R_1$, and a later split
can shed the extras into a sub-relation that is then contained in
$R_2$. The key-centric version picks the *smallest* key candidate by
construction, so $(\star)$ formally rules out extraneous attributes.

## Summary

The FD-centric reading of BCNF decomposition obscures the actual
object of interest: sets of attributes that are not yet keys. Reading
the algorithm key-centrically — find an $X$ you can promote to a key,
promote it, repeat — collapses the BCNF check, the decomposition step,
and the correctness arguments into a single pattern:

| | Singleton $F$ | General $F$ |
|---|---|---|
| Key candidate | single attribute $A$ with $\{A\} \subsetneq \mathrm{reach}(A) \cap S \subsetneq S$ | subset $X$ with $X \subsetneq X^+ \cap S \subsetneq S$ |
| How to find one | scan LHS attributes of $F$ | iterate subsets small to large |
| Split | $S_1 = \mathrm{reach}(A) \cap S$, $S_2 = (S \setminus \mathrm{reach}(A)) \cup \{A\}$ | $S_1 = X^+ \cap S$, $S_2 = (S \setminus X^+) \cup X$ |
| After the split | $A$ is a key of $S_1$ | $X$ is a key of $S_1$ |
| Uniqueness | yes, when $G_F$ is a forest | not in general |
| Non-redundancy | automatic (pivots are single attributes) | automatic when picking the *minimal* key candidate |

Same algorithm, different granularity, same idea: decomposition is the
act of turning a would-be key into an actual one.
