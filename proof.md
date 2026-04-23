# BCNF for singleton FDs: a reachability check on attributes

## Motivation

The textbook BCNF check considers every nontrivial FD in $F^+$, which in
principle requires iterating over the powerset of attributes for the LHS.
In a classroom or exam setting this is painful to do by hand. The result
below shows that when the input FD set $F$ is **singleton** (one attribute
on each side), BCNF status reduces to a check on *attributes*: for each
attribute $A$, does $A$'s reachable set in the FD graph equal $\{A\}$ or
the whole schema? The same check applies to every sub-relation during
decomposition, using the original FD graph throughout — no projection,
no acyclicity, no powerset. The student works entirely with one picture:
the FD graph $G_F$.

## Setup

- $R$ is a relation with attribute set $\mathcal{U}$.
- $F$ is a set of FDs, each of the form $A \to B$ with $A, B \in \mathcal{U}$
  and $A \neq B$ (**singleton**: one attribute on each side).
- $G_F = (\mathcal{U}, E)$ is the FD graph, $E = \{(A,B) : A \to B \in F\}$.
  (Not required to be acyclic.)
- $\mathrm{reach}(A)$ is the set of nodes reachable from $A$ in $G_F$
  (including $A$, via the empty path).
- $X^+$ is the attribute closure of $X \subseteq \mathcal{U}$ under $F$.
- For $S \subseteq \mathcal{U}$, $X$ is a **superkey of $S$** (under the
  FDs that hold on $S$) iff $X \cup (X^+ \cap S) = S$; equivalently
  $X^+ \supseteq S$.
- An FD $X \to Y$ is **nontrivial** iff $Y \not\subseteq X$, and
  **violates BCNF on $S$** iff it is nontrivial, $X \cup Y \subseteq S$,
  and $X$ is not a superkey of $S$.

## Closure is reachability

**Lemma 1.** For singleton $F$,
$$
X^+ \;=\; \bigcup_{A \in X} \mathrm{reach}(A).
$$

*Proof.* Compute $X^+$ stepwise: $X_0 = X$, and
$X_{i+1} = X_i \cup \{C : \exists\, A \in X_i \text{ with } A \to C \in F\}$.
Because every FD has a singleton LHS, the firing condition is "some single
attribute already in $X_i$", not "some set of attributes".

(⊇) For $A \in X$ and $B \in \mathrm{reach}(A)$, take a path
$A = A_0 \to A_1 \to \cdots \to A_k = B$ in $G_F$. Then $A_0 \in X_0$ and
each edge $A_i \to A_{i+1} \in F$ puts $A_{i+1}$ into $X_{i+1}$, so
$B \in X_k \subseteq X^+$.

(⊆) Induct on the smallest $i$ with $B \in X_i$. If $i = 0$, then
$B \in X$ and is reachable from itself by the empty path. If $i \ge 1$,
there is a witness $A \to B \in F$ with $A \in X_{i-1}$; by the inductive
hypothesis $A \in \mathrm{reach}(A_0)$ for some $A_0 \in X$, and appending
the edge $A \to B$ gives $B \in \mathrm{reach}(A_0)$. $\blacksquare$

## The attribute-level BCNF criterion

The main result, stated directly at the sub-relation level:

**Theorem.** For singleton $F$ and any $S \subseteq \mathcal{U}$,
$$
S \text{ is in BCNF} \quad \Longleftrightarrow \quad
\text{for every } A \in S,\; \mathrm{reach}(A) \cap S \in \{\{A\},\, S\}.
$$

Intuition: in the FD graph, each attribute either reaches nothing new in
$S$ (no outgoing derivation to worry about) or reaches all of $S$ (its
LHS is a superkey, so any FD it gets into does not violate BCNF). Anything
in between is exactly a BCNF violation.

Because attributes that are not the LHS of any FD in $F$ have
$\mathrm{reach}(A) = \{A\}$ and trivially pass, the check only needs to
inspect LHS attributes of input FDs — the same finite list $F$ gives
you, at every recursion level.

*Proof.*

**(⇒)** Suppose $S$ is in BCNF. Fix $A \in S$. If $\mathrm{reach}(A) \cap S = \{A\}$,
we are done. Otherwise pick $B \in \mathrm{reach}(A) \cap S$ with
$B \neq A$. By Lemma 1, $B \in A^+$, so $\{A\} \to \{B\}$ is a nontrivial
FD in $\pi_S(F^+)$. BCNF forces $A$ to be a superkey of $S$, i.e.,
$A^+ \supseteq S$, which by Lemma 1 gives $\mathrm{reach}(A) \supseteq S$,
so $\mathrm{reach}(A) \cap S = S$.

**(⇐)** Suppose every $A \in S$ has $\mathrm{reach}(A) \cap S \in \{\{A\}, S\}$.
Let $X \to Y$ be a nontrivial FD in $\pi_S(F^+)$, so
$X, Y \subseteq S$ and $Y \not\subseteq X$. Pick $B \in Y \setminus X$;
then $B \in X^+ \cap S$. By Lemma 1, $B \in \mathrm{reach}(A_0)$ for some
$A_0 \in X$. Since $A_0 \in X \subseteq S$ and $B \in S$ with $B \neq A_0$
(as $B \notin X$), $\mathrm{reach}(A_0) \cap S \ni B \neq A_0$, so it is
not $\{A_0\}$. By hypothesis it must equal $S$. Thus
$X^+ \supseteq \mathrm{reach}(A_0) \supseteq S$, making $X$ a superkey of
$S$.

Hence every nontrivial FD in $\pi_S(F^+)$ has a superkey LHS: $S$ is in
BCNF. $\blacksquare$

## What this means for decomposition

The theorem is a closed statement about any attribute subset $S$ — it
makes no reference to a decomposition history, which is why it works
recursively at every step. Each BCNF decomposition step looks like:

1. Current sub-relation has attribute set $S$ (initially $\mathcal{U}$).
2. For each attribute $A \in S$ that is the LHS of some FD in $F$,
   compute $\mathrm{reach}(A) \cap S$ once (linear-time BFS/DFS on $G_F$,
   then intersect with $S$).
3. If every such $A$ has $\mathrm{reach}(A) \cap S \in \{\{A\}, S\}$, the
   theorem says $S$ is in BCNF — emit it and stop this branch.
4. Otherwise pick any violating $A$, i.e., one with
   $\{A\} \subsetneq \mathrm{reach}(A) \cap S \subsetneq S$. Split $S$
   into
   $$S_1 = \mathrm{reach}(A) \cap S \qquad \text{and} \qquad S_2 = (S \setminus \mathrm{reach}(A)) \cup \{A\},$$
   and recurse on each. ($S_1$ is the BCNF-style splitter "$A$ together
   with its closure"; $S_2$ keeps $A$ as the attribute linking the two
   halves.)

The whole procedure reads the graph $G_F$ once. No projection of FDs,
no recomputation of closures in a new FD system, no enumeration of
subsets, and no acyclicity assumption.

## Remark: reconciling with the FD-centric view

The FD-centric version of the theorem on the top-level relation —
"$R$ is in BCNF iff every $A \to B \in F$ has $A$ as a superkey" — is
the special case $S = \mathcal{U}$: for $A$ that is an LHS of some FD,
$\mathrm{reach}(A) \supsetneq \{A\}$, so the attribute-level check
reduces to $\mathrm{reach}(A) = \mathcal{U}$, i.e., $A$ is a superkey.
Attributes that appear on no LHS trivially pass. The attribute-level
statement is what generalizes cleanly to sub-relations, because
$\mathrm{reach}(A) \cap S$ is read directly from the original graph
$G_F$ rather than from a projected FD set.
