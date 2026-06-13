# The Elizalde–Luo conjecture for {1132, 3312}: a complete proof

**Statement proved.** For every $n \ge 1$, the number of nonnesting permutations of the
multiset $[n]_2 = \{1,1,2,2,\dots,n,n\}$ that avoid the patterns $1132$ and $3312$ equals
$$ a_n \;=\; 3^n - 3\cdot 2^{n-1} + 1 .$$
(Conjectured by Elizalde and Luo, arXiv:2412.00336 / DMTCS 27:1 (2025), Table 4; OEIS
A168583 shifted. All conventions are pinned in `../DEFINITIONS.md` and are repeated below.)

**Method.** Structural normal form (Dyck shape $\times$ label permutation), reduction of
the two pattern conditions to (i) a classical pattern condition on the label permutation
and (ii) a local "sign-coupling" constraint system attached to the shape, factorization
over irreducible Dyck components, a complete classification of the components with
solutions, and a weighted finite automaton / transfer matrix whose generating function is
$$A(z) \;=\; \frac{z\,(1-2z+3z^2)}{(1-z)(1-2z)(1-3z)}
       \;=\; \frac{3z}{1-3z}-\frac{3z}{1-2z}+\frac{z}{1-z},$$
giving $a_n = 3^n - 3\cdot2^{n-1}+1$ and the recurrence
$a_n = 6a_{n-1} - 11a_{n-2} + 6a_{n-3}$ ($n\ge 4$), $a_1=1,\ a_2=4,\ a_3=16$.

Every lemma below has been verified exhaustively by machine on top of the project's
vetted ground-truth enumerations; the validation log is Section 10. The proof itself is
self-contained and elementary (finite case analysis, explicit bijections, formal power
series); it is designed to be Lean-formalizable.

---

## 0. Conventions

* A **word** is $w = w_1 w_2 \cdots w_{2n}$ over $\{1,\dots,n\}$ using each letter exactly
  twice (a permutation of $[n]_2$).
* **Containment** (Elizalde–Luo, biconditional convention): $w$ contains the pattern
  $\sigma = \sigma_1\cdots\sigma_k$ iff there are indices $i_1<\cdots<i_k$ with
  $w_{i_r} < w_{i_s} \Leftrightarrow \sigma_r < \sigma_s$ **and**
  $w_{i_r} = w_{i_s} \Leftrightarrow \sigma_r = \sigma_s$ for all $r,s$.
  $w$ **avoids** $\sigma$ iff it does not contain it.
* $w$ is **nonnesting** iff it avoids $1221$ and $2112$, i.e. there are no indices
  $i_1<i_2<i_3<i_4$ with $w_{i_1}=w_{i_4} \ne w_{i_2}=w_{i_3}$.
* For a value $v$, write $o(v)$, $c(v)$ for the positions of its first and second
  occurrence in $w$ (its **opener** and **closer**).
* $a_n$ counts nonnesting $w$ avoiding both $1132$ and $3312$. Raw words are counted
  (no quotient by relabeling; see DEFINITIONS.md §5).
* A **Dyck word** of length $2n$ is $s\in\{\mathrm U,\mathrm D\}^{2n}$ with $n$ U's, $n$
  D's, and every prefix containing at least as many U's as D's.
* For permutations (all letters distinct), patterns $132$ and $312$ have their classical
  meaning, which agrees with the biconditional convention above.

Throughout, "arc $i$" refers to the pair (the $i$-th U, the $i$-th D) of a Dyck word; we
write $o_i$ for the position of the $i$-th U and $c_i$ for the position of the $i$-th D.
So $o_1 < o_2 < \cdots < o_n$ and $c_1 < \cdots < c_n$.

**Fact 0.1 (i-th U before i-th D).** In a Dyck word, $o_i < c_i$ for all $i$.
*Proof.* The prefix ending at $c_i$ contains $i$ D's, hence at least $i$ U's by the
prefix-dominance property; therefore the $i$-th U occurs at a position $\le c_i$, and
$o_i \ne c_i$, so $o_i < c_i$. $\square$

---

## 1. Normal form: Dyck shape times label permutation

**Lemma 1.** The map
$$ (s, p) \;\longmapsto\; w(s,p), \qquad
   w(s,p) := \text{the word with letter } p_i \text{ at the } i\text{-th U and at the }
   i\text{-th D of } s, $$
is a bijection from (Dyck words $s$ of length $2n$) $\times$ (permutations $p$ of $[n]$)
onto the set of nonnesting permutations of $[n]_2$. Under this bijection the two
occurrences of $p_i$ are at positions $o_i < c_i$ (its opener is the $i$-th U).

*Proof.* (a) *$w(s,p)$ is a well-defined word with first occurrences at U's.* By Fact
0.1, $o_i< c_i$, so the first occurrence of $p_i$ is at the $i$-th U. Each letter is used
twice.

(b) *$w(s,p)$ is nonnesting.* Suppose $w_{i_1}=w_{i_4} \ne w_{i_2}=w_{i_3}$ with
$i_1<i_2<i_3<i_4$. The two equal pairs are the endpoint pairs of two arcs, say arcs $i$
(at $i_1<i_4$) and $j$ (at $i_2<i_3$); so $o_i < o_j$ and $c_j < c_i$, i.e. $i<j$ and
$j<i$, a contradiction.

(c) *Surjectivity.* Let $w$ be nonnesting. Let $s(w)$ mark first occurrences U and second
occurrences D; $s(w)$ is a Dyck word (every prefix has $\#\mathrm U\ge\#\mathrm D$,
because each value closed in the prefix was opened in it). Claim: in $w$, the value with
the $i$-th closer equals the value with the $i$-th opener. If not, there are values
$u \ne v$ with $o(u) < o(v)$ but $c(v) < c(u)$. Then
$o(u) < o(v) < c(v) < c(u)$ (using $o(v) < c(v)$), so the subsequence at positions
$o(u),o(v),c(v),c(u)$ is $u\,v\,v\,u$, an occurrence of $1221$ (if $u<v$) or $2112$ (if
$u>v$), contradicting nonnesting. Hence, defining $p_i :=$ the value whose opener is the
$i$-th U, we get $p$ a permutation of $[n]$ (one value per arc) with the $i$-th closer
also labeled $p_i$, i.e. $w = w(s(w), p)$.

(d) *Injectivity.* $s$ is recovered from $w(s,p)$ as the first-occurrence indicator, and
$p_i$ is the letter at the $i$-th U. $\square$

From now on, fix $n$, a Dyck word $s$ with arcs $(o_i,c_i)_{i=1}^n$, a permutation $p$,
and $w = w(s,p)$.

---

## 2. The avoidance conditions in arc language

**Fact 2.1 (occurrence normal form).** $w$ contains $1132$ iff there exist a value $a$
and positions $k<l$ with $c(a) < k$ and $w_k > w_l > a$. $w$ contains $3312$ iff there
exist a value $a$ and positions $k<l$ with $c(a) < k$ and $w_k < w_l < a$.

*Proof.* In any occurrence $i_1<i_2<i_3<i_4$ of $1132$, the biconditional convention
forces $w_{i_1}=w_{i_2}$ and $w_{i_1} < w_{i_4} < w_{i_3}$, nothing else. Since each value
occurs exactly twice, $w_{i_1}=w_{i_2}$ forces $i_1 = o(a)$, $i_2 = c(a)$ for
$a:=w_{i_1}$. So an occurrence is exactly: a value $a$ and positions $k:=i_3<l:=i_4$ with
$k > c(a)$ and $w_k > w_l > a$. (Conversely such data is an occurrence, taking
$i_1 = o(a) < i_2 = c(a)$.) Same for $3312$ with $w_k < w_l < a$. $\square$

Define two conditions on the pair $(s,p)$:

* **(P1)** $p$ avoids the permutation patterns $132$ and $312$; explicitly, there are no
  arc indices $i<j<k$ with $p_i < p_k < p_j$ (a $132$) or $p_j < p_k < p_i$ (a $312$).
* **(P2)** for all arc indices $i<k<j$ with $c_i < o_j < c_k$ (arc $i$ closes before arc
  $j$ opens, and arcs $k,j$ cross):
  $\min(p_k,p_j) < p_i < \max(p_k,p_j)$.

**Lemma 2.** $w(s,p)$ avoids $\{1132, 3312\}$ $\iff$ (P1) and (P2) hold.

*Proof.* By Fact 2.1, $w$ contains one of the two patterns iff there exist an arc $i$
(value $a = p_i$, closer $c_i$) and positions $k < l$ with $c_i < k$ such that
$$(\mathrm{D}):\ p_i < w_l < w_k \qquad\text{or}\qquad (\mathrm{A}):\ w_k < w_l < p_i .$$

**($\Rightarrow$, contrapositive: ¬P1 or ¬P2 gives an occurrence.)**

*¬(P1).* Suppose $p_i < p_k < p_j$ with $i<j<k$. Take positions $(c_j, c_k)$: they
satisfy $c_i < c_j < c_k$ and $w_{c_j} = p_j > w_{c_k} = p_k > p_i$, which is (D), an
occurrence of $1132$. If $p_j < p_k < p_i$, the same positions give (A), an occurrence
of $3312$.

*¬(P2).* Suppose $i<k<j$, $c_i < o_j < c_k$, and $p_i$ is **not** strictly between
$p_k$ and $p_j$ (note $p_i\notin\{p_k,p_j\}$). Four subcases:
  - $p_i < \min$ and $p_k < p_j$: positions $(o_j, c_k)$: $c_i < o_j < c_k$ and
    $w_{o_j} = p_j > w_{c_k} = p_k > p_i$ — (D), a $1132$.
  - $p_i < \min$ and $p_j < p_k$: positions $(c_k, c_j)$: $c_i < c_k < c_j$ and
    $p_k > p_j > p_i$ — (D), a $1132$.
  - $p_i > \max$ and $p_k < p_j$: positions $(c_k, c_j)$: $p_k < p_j < p_i$ — (A), a
    $3312$.
  - $p_i > \max$ and $p_j < p_k$: positions $(o_j, c_k)$: $p_j < p_k < p_i$ — (A), a
    $3312$.

**($\Leftarrow$: P1 and P2 exclude every occurrence.)** Suppose arc $i$ and positions
$k<l$, $c_i < k$, realize (D) or (A). Then $w_k \ne w_l$, so $k,l$ are endpoints of two
distinct arcs $j \ne h$: $k \in \{o_j, c_j\}$, $l \in \{o_h, c_h\}$, $w_k = p_j$,
$w_l = p_h$. We check all cases; in each, (D) reads $p_i < p_h < p_j$ and (A) reads
$p_j < p_h < p_i$.

1. $k = c_j$, $l = c_h$. Then $c_i < c_j < c_h$, so $i<j<h$. (D) is a $132$ at
   $(i,j,h)$; (A) is a $312$ at $(i,j,h)$. Both contradict (P1).
2. $k = c_j$, $l = o_h$. From $o_h > c_j$: if $h \le j$ then $o_h < c_h \le c_j$,
   absurd; so $h > j$, and $c_i < c_j$ gives $i < j < h$. (D)/(A) again contradict (P1).
3. $k = o_j$, $l = o_h$. Then $o_j < o_h$, so $j < h$; and $c_i < o_j < c_j$ gives
   $i<j$. (D)/(A) contradict (P1) at $(i,j,h)$.
4. $k = o_j$, $l = c_h$ with $h > j$. Then $i < j < h$ as in case 3; (D)/(A) contradict
   (P1).
5. $k = o_j$, $l = c_h$ with $h < j$. Then $o_j < c_h$ (positions increase) and
   $c_h > o_j > c_i$ gives $h > i$; so $i < h < j$ with $c_i < o_j < c_h$: the triple
   $(i, h, j)$ is exactly a (P2) triple, so $p_i$ is strictly between $p_h$ and $p_j$.
   But (D) says $p_i < p_h < p_j$ ($p_i$ below both) and (A) says $p_j < p_h < p_i$
   ($p_i$ above both) — both contradict betweenness.

   ($h = j$ would give $w_k = w_l$, excluded.) $\square$

---

## 3. Sign encoding of Av(132, 312)

**Lemma 3.** Let $p$ be a permutation of $[n]$.
(a) $p$ avoids $\{132, 312\}$ $\iff$ for every $m \ge 2$, $p_m = \max(p_1..p_m)$ or
$p_m = \min(p_1..p_m)$ ("$p$ is prefix-extremal").
(b) For prefix-extremal $p$ define $\varepsilon_m(p) := +1$ if $p_m=\max(p_1..p_m)$,
$-1$ if $p_m=\min(p_1..p_m)$ ($2\le m\le n$; the two cases are exclusive since $m\ge2$).
Then $p \mapsto (\varepsilon_2,\dots,\varepsilon_n)$ is a bijection from prefix-extremal
permutations of $[n]$ onto $\{\pm1\}^{n-1}$. In particular there are $2^{n-1}$ of them.

*Proof.* (a) ($\Leftarrow$) Suppose $p$ has an occurrence of $132$: $q<r<m$ with
$p_q < p_m < p_r$. Then $p_m$ is neither the max (it is $< p_r$) nor the min (it is
$> p_q$) of $p_1..p_m$, contradiction. A $312$ ($p_r < p_m < p_q$) likewise.
($\Rightarrow$) Suppose $p_m$ ($m\ge2$) is neither prefix-max nor prefix-min: there are
$q, r < m$ with $p_q < p_m < p_r$. If $q < r$, $(q,r,m)$ is a $132$; if $r < q$,
$(r,q,m)$ is a $312$.

(b) *Injectivity and surjectivity by downward induction on $n$.* If $\varepsilon_n=+1$,
then $p_n = \max(p_1..p_n) = n$ is forced; if $\varepsilon_n=-1$, $p_n=1$ is forced.
Deleting $p_n$ leaves a sequence on the value set $[n]\setminus\{p_n\}$ (an interval),
which is order-isomorphic to a permutation of $[n-1]$; its prefixes for $m\le n-1$ are
unchanged, so it is prefix-extremal with sign vector $(\varepsilon_2..\varepsilon_{n-1})$,
and every prefix-extremal permutation of $[n]$ with the given $\varepsilon_n$ arises from
exactly one such shorter permutation by appending the forced value. The base $n=1$ is the
unique $p=(1)$ with empty sign vector. $\square$

We extend the sign vector by the convention $\varepsilon_1 := +1$; $\varepsilon_1$ will
never be constrained, and $p$ depends only on $(\varepsilon_2,\dots,\varepsilon_n)$.

---

## 4. (P2) as a sign-constraint system

For the shape $s$, define for each arc $j$:
$$ \beta_j \;:=\; \#\{\text{D's before the } j\text{-th U}\}
            \;=\; \#\{i : c_i < o_j\} .$$
Since closers are increasing, the arcs closing before $o_j$ are exactly $1,\dots,\beta_j$,
and the arcs $k<j$ with $c_k > o_j$ (the arcs **open** when arc $j$ opens) are exactly
$k \in \{\beta_j+1, \dots, j-1\}$.

**Definition (constraint system $E(s)$).** For $\varepsilon\in\{\pm1\}^n$:
$$E(s):\qquad \text{for every arc } j \text{ with } \beta_j\ge 1:\quad
\varepsilon_k = -\varepsilon_j \ \ \text{for all } k \text{ with } \beta_j < k < j. $$
(If $\beta_j = j-1$ the inner condition is vacuous; if $\beta_j=0$ there is no condition
for $j$.) Note every constraint has $2 \le k < j$ (since $k > \beta_j \ge 1$), so
$\varepsilon_1$ is never constrained.

**Lemma 4.** Let $p$ be prefix-extremal with sign vector $\varepsilon$. Then (P2) holds
for $(s,p)$ $\iff$ $\varepsilon$ satisfies $E(s)$.

*Proof.* The (P2) triples with a fixed third index $j$ are exactly: $i \le \beta_j$ and
$\beta_j < k < j$ (by the paragraph above: $c_i < o_j \iff i\le\beta_j$, and
$o_j < c_k,\ k<j \iff \beta_j<k<j$). So it suffices to fix $j$ with
$1 \le \beta_j \le j-2$ (otherwise both sides are vacuous for this $j$) and prove
$$ \bigl[\forall i\le \beta_j,\ \forall k\in(\beta_j,j):\
   \min(p_k,p_j)<p_i<\max(p_k,p_j)\bigr]
   \iff
   \bigl[\forall k\in(\beta_j,j):\ \varepsilon_k=-\varepsilon_j\bigr]. $$
Write $b := \beta_j \ge 1$. By symmetry (the value-complement $p_m \mapsto n+1-p_m$ is a
bijection of prefix-extremal permutations negating all signs and preserving both sides),
assume $\varepsilon_j = +1$, i.e. $p_j = \max(p_1..p_j)$, so $p_i < p_j$ for all $i<j$.

($\Leftarrow$) Assume $\varepsilon_k = -1$ for all $k\in(b,j)$. Fix such $k$ and any
$i \le b$. Then $p_k = \min(p_1..p_k)$ and $i < k$, so $p_k < p_i$; and $p_i < p_j$.
Hence $p_k < p_i < p_j$: betweenness holds.

($\Rightarrow$) Assume betweenness for all $i \le b$, $k\in(b,j)$. Fix $k$. Since
$p_i < p_j$, betweenness forces $p_k < p_i$ for every $i\le b$; in particular
$p_k < p_1$ (here $b\ge1$ is used). If $\varepsilon_k=+1$ then
$p_k = \max(p_1..p_k) \ge p_1 > p_k$, absurd; so $\varepsilon_k = -1 = -\varepsilon_j$.
$\square$

**Theorem 5 (complete characterization).** The map
$(s, \varepsilon) \mapsto w(s, p(\varepsilon))$, where $p(\varepsilon)$ is the
prefix-extremal permutation with sign vector $(\varepsilon_2..\varepsilon_n)$, is a
bijection
$$ \{(s,\varepsilon):\ s \text{ Dyck word of length } 2n,\
   \varepsilon\in\{+1\}\times\{\pm1\}^{n-1} \text{ satisfying } E(s)\}
   \;\longleftrightarrow\;
   \{\text{nonnesting } w \text{ avoiding } 1132, 3312\}. $$
Consequently, writing $\mathrm{Sol}(E(s)) \subseteq \{\pm1\}^n$ for the full solution set
(both values of $\varepsilon_1$ allowed),
$$ a_n \;=\; \sum_{s} \tfrac12\,\bigl|\mathrm{Sol}(E(s))\bigr| . $$

*Proof.* Combine Lemmas 1–4: avoiders $=$ $\{w(s,p)\}$ with $p$ prefix-extremal
(Lemma 2 (P1) + Lemma 3) and (P2) $\iff E(s)$ (Lemma 4). The map is injective because
$(s,p)\mapsto w$ is (Lemma 1) and $\varepsilon \mapsto p$ is (Lemma 3). Since no
constraint of $E(s)$ involves $\varepsilon_1$, $|\mathrm{Sol}(E(s))| =
2\cdot\#\{(\varepsilon_2..\varepsilon_n) \text{ valid}\}$. $\square$

*(Machine check: Lemmas 2 and 4 verified for every $(s,p)$ pair, $n\le 7$ — 2,162,160
pairs at $n=7$ — and the bijection of Theorem 5 verified by exact set equality of the two
sides for $n \le 7$. See Section 10, items V1–V3.)*

---

## 5. Factorization over irreducible components

A Dyck word factors uniquely as $s = c^{(1)} c^{(2)} \cdots c^{(r)}$ where each
$c^{(\ell)}$ is **irreducible** (nonempty, returns to height 0 exactly at its end). The
factorization is at the returns to height 0. Let $m_\ell$ be the number of arcs of
$c^{(\ell)}$ and $M_\ell = m_1+\cdots+m_\ell$ ($M_0=0$); the arcs of component $\ell$
are $A_\ell = \{M_{\ell-1}+1, \dots, M_\ell\}$ (openers and closers of a component are
the U's and D's inside it, since the height is 0 at its boundary).

For an irreducible Dyck word $c$ with $m$ arcs (arcs renumbered $1..m$, with
$\beta^c_j$ = closers of $c$ before the $j$-th opener of $c$), define two constraint
systems on $\delta \in \{\pm1\}^m$:

* **first-type** $E^{\mathrm{fst}}(c)$: for every $j$ with $\beta^c_j \ge 1$:
  $\delta_k = -\delta_j$ for all $\beta^c_j < k < j$;
* **all-type** $E^{\mathrm{all}}(c)$: for **every** $j \ge 2$:
  $\delta_k = -\delta_j$ for all $\beta^c_j < k < j$.

Let $N(c) := |\mathrm{Sol}(E^{\mathrm{fst}}(c))|$ and
$M(c) := |\mathrm{Sol}(E^{\mathrm{all}}(c))|$.

**Lemma 6 (factorization).** For $s = c^{(1)}\cdots c^{(r)}$:
$$ |\mathrm{Sol}(E(s))| \;=\; N(c^{(1)}) \cdot \prod_{\ell=2}^{r} M(c^{(\ell)}). $$

*Proof.* Fix arc $j \in A_\ell$ and compare its $E(s)$-constraints with the
within-component constraints. All arcs of components $1..\ell-1$ close before component
$\ell$ starts, and no later arc opens before $o_j$; hence
$\beta_j = M_{\ell-1} + \beta^{c^{(\ell)}}_{j'}$ where $j' := j - M_{\ell-1}$ is the
within-component index. The constrained range $(\beta_j, j)$ translates to
$(\beta^c_{j'}, j')$ inside $A_\ell$; in particular every constraint of $E(s)$ couples
only variables within one component. Activation: for $\ell = 1$, $\beta_j \ge 1 \iff
\beta^c_{j'} \ge 1$ (first-type); for $\ell \ge 2$, $\beta_j \ge M_{\ell-1} \ge 1$
always, so the constraint is active for every $j' \ge 2$, and for $j'=1$ the range
$(\beta^c_1, 1) = (0,1)$ is empty (all-type). Thus $E(s)$ is the disjoint union of
$E^{\mathrm{fst}}(c^{(1)})$ and $E^{\mathrm{all}}(c^{(\ell)})$, $\ell\ge2$, on disjoint
variable blocks, and the solution sets multiply. $\square$

---

## 6. Classification of the components

Throughout this section $c$ is irreducible with $m$ arcs and we use two facts:

**Fact 6.0.** (a) In an irreducible $c$, for every $j \in \{2,\dots,m\}$ the height just
before the $j$-th U is $\ge 1$; equivalently $\beta^c_j \le j-2$, equivalently arc $j-1$
is still open when arc $j$ opens (so the range $(\beta^c_j, j)$ always contains $j-1$).
*Proof:* the height before the $j$-th U equals $(j-1)-\beta^c_j$; if it were 0 at that
interior position, $c$ would return to 0 before its end. (b) $\beta^c_2 = 0$.
*Proof:* $\beta^c_2 \le 2-2 = 0$ by (a).

### 6a. Non-first components

**Lemma 7a.** $M(c) = 2$ if $c = \mathrm U(\mathrm{UD})^{m-1}\mathrm D$, and $M(c) = 0$
otherwise.

*Proof.* **(Shapes $\mathrm U(\mathrm{UD})^{m-1}\mathrm D$ have $M = 2$.)** Here the U's
are at positions $1, 2, 4, \dots, 2m-2$ and the D's at $3, 5, \dots, 2m-1, 2m$. So
$\beta^c_j = j - 2$ for $2 \le j \le m$ (the D's before position $2j-2$ are
$3,5,\dots,2j-3$, which number $j-2$), and each constrained range is
$(j-2, j) = \{j-1\}$. The system is exactly
$\delta_{j} = -\delta_{j-1}$ ($2\le j\le m$): $\delta_1$ free, the rest forced —
$M(c)=2$.

**(Everything else has $M = 0$.)** Suppose $\mathrm{Sol}(E^{\mathrm{all}}(c)) \neq
\emptyset$, with solution $\delta$, and suppose $c$ is not of the stated form; then (see
next paragraph) some $j$ has $\beta^c_j \le j-3$; choose $j$ minimal. By Fact 6.0(b),
$j \ge 3$. Both $j-1$ and $j-2$ lie in $(\beta^c_j, j)$, so
$\delta_{j-2} = -\delta_j = \delta_{j-1}$. By minimality, $\beta^c_{j-1} = (j-1)-2$
(Fact 6.0(a) gives $\le$; minimality gives $\ge$), so the constraint for $j-1$ is
$\delta_{j-2} = -\delta_{j-1}$ — contradicting $\delta_{j-2} = \delta_{j-1}$ (signs are
$\pm1$). Hence $\beta^c_j = j-2$ for all $2\le j\le m$. This pins the shape: the $j$-th
U is preceded by exactly $j-1$ U's $+$ $(j-2)$ D's, i.e. $o_j = 2j-2$ for $j \ge 2$ and
$o_1=1$; the D's occupy the remaining positions. That is precisely
$c = \mathrm U(\mathrm{UD})^{m-1}\mathrm D$. $\square$

### 6b. First components

**Lemma 7b.** Let $c$ be irreducible with $m$ arcs and initial U-run of length $a$
($\ge 1$). Then $N(c) \ne 0$ exactly in the following cases:

| type | shape | parameters | $N(c)$ |
|---|---|---|---|
| (i) | $\mathrm U^a \mathrm D^a$ | $a = m \ge 1$ | $2^a$ |
| (ii) | $\mathrm U^a \mathrm D^x \mathrm U \mathrm D^{\,a-x+1}$ | $m = a+1$, $a\ge2$, $1\le x\le a-1$ | $2^{x+1}$ |
| (iii) | $\mathrm U^a \mathrm D^x \mathrm U \mathrm D^{\,a-x} \mathrm U (\mathrm{DU})^{t-2} \mathrm D^2$ | $m = a+t$, $t\ge2$, $a\ge2$, $1\le x\le a-1$ | $2^{x+1}$ |

*Proof.* Arcs $1,\dots,a$ have $\beta^c_j = 0$ (their openers precede the first D), so
they carry no constraints. Let $t := m - a \ge 0$.

**$t=0$.** Then after $\mathrm U^a$ there are no more U's, so $c = \mathrm U^a\mathrm
D^a$: no constraints at all, $N = 2^m = 2^a$ — type (i).

**$t\ge1$.** Let $x := \beta^c_{a+1}$, the number of D's before the $(a{+}1)$-st U. Then
$x \ge 1$ ($o_{a+1}$ lies after the first D-run) and $x \le (a+1)-2 = a-1$ (Fact
6.0(a)); in particular $a \ge 2$. The constraint for $j = a+1$ is
$$ \delta_{x+1} = \delta_{x+2} = \cdots = \delta_a = -\delta_{a+1} \;=:\; v
   \quad(\text{common value}). \tag{6.1}$$

**$t=1$.** After $o_{a+1}$ there are only D's, and the total number of D's is $m=a+1$, so
$c = \mathrm U^a\mathrm D^x\mathrm U\mathrm D^{\,a-x+1}$ — type (ii). The system is
exactly (6.1): free variables $\delta_1..\delta_x$ and $v$, with $\delta_{a+1}=-v$
forced: $N = 2^{x+1}$.

**$t\ge2$.** Consider $j = a+2$. By Fact 6.0(a), $a+1 \in (\beta^c_{a+2}, a+2)$, so the
constraint forces $\delta_{a+1} = -\delta_{a+2}$, i.e. $\delta_{a+2} = v$. If
$\beta^c_{a+2} \le a-1$, then also $a \in (\beta^c_{a+2}, a+2)$, forcing $\delta_a =
-\delta_{a+2} = -v$; but $\delta_a = v$ by (6.1) — contradiction. So for a solution to
exist, $\beta^c_{a+2} = a$: all of arcs $x+1..a$ close before $o_{a+2}$, i.e. there are
exactly $a - x$ D's between the $(a{+}1)$-st and $(a{+}2)$-nd U.

Next, for $j \ge a+3$ we claim $\beta^c_j = j-2$ (exactly one D between consecutive U's
from the $(a{+}2)$-nd on). Otherwise pick $j \ge a+3$ minimal with $\beta^c_j \le j-3$:
then $j-1, j-2 \in (\beta^c_j, j)$ give $\delta_{j-2} = \delta_{j-1}$, while the
constraint for $j-1$ — whose range is $\{j-2\}$, because $\beta^c_{j-1} = (j-1)-2$
(for $j-1 = a+2$ this is the previous paragraph; for $j-1 > a+2$, minimality) — gives
$\delta_{j-2} = -\delta_{j-1}$: contradiction. After the last U, the path is at height
$2$ (arcs $m-1, m$ open: indeed $\beta^c_m = m - 2$), so the word ends $\mathrm D^2$.
This is exactly type (iii):
$c = \mathrm U^a\mathrm D^x\mathrm U\mathrm D^{\,a-x}\mathrm U(\mathrm{DU})^{t-2}
\mathrm D^2$.

Conversely, on a type-(iii) shape the constraint system is exactly (6.1) together with
$\delta_j = -\delta_{j-1}$ for $a+2 \le j \le m$ (computing $\beta^c$: $\beta^c_{a+2}=a$
gives range $\{a+1\}$; $\beta^c_j = j-2$ gives range $\{j-1\}$). The solutions: choose
$\delta_1..\delta_x$ freely and $v$ freely; then $\delta_{x+1..a} = v$,
$\delta_{a+1} = -v$, $\delta_{a+2} = v$, alternating — all constraints hold. So
$N = 2^{x+1}$, and in the non-classified shapes the contradictions above show $N=0$.
$\square$

*(Machine check: Lemmas 6, 7a, 7b verified against brute-force solution counts for every
irreducible component with $\le 8$ arcs and against the per-shape ground-truth avoider
counts (independent Rust enumeration) for every Dyck shape with $n \le 8$ — 1430 shapes
at $n=8$. See Section 10, items V4–V5.)*

---

## 7. Counting: generating functions

All series are formal power series in $\mathbb Q[[z]]$; $z$ marks arcs. By Theorem 5 and
Lemma 6, summing over the (unique) component factorization:
$$ A(z) := \sum_{n\ge1} a_n z^n
   = \tfrac12 \sum_{r\ge1}\ \sum_{\substack{c^{(1)},\dots,c^{(r)}\\ \text{irreducible}}}
     N(c^{(1)})\, z^{m_1} \prod_{\ell=2}^r M(c^{(\ell)})\, z^{m_\ell}
   = \tfrac12\, \frac{F(z)}{1 - G(z)}, $$
where $F(z) := \sum_{c} N(c)\, z^{m(c)}$ and $G(z) := \sum_c M(c)\, z^{m(c)}$ over
irreducible $c$. (The rearrangement is the standard sequence construction: every Dyck
word is a unique sequence of irreducible ones, and both weights are multiplicative.)

**$G$:** by Lemma 7a, $G(z) = \sum_{m\ge1} 2 z^m = \dfrac{2z}{1-z}$.

**$F$:** by Lemma 7b,
$$ F(z) = \underbrace{\sum_{a\ge1} 2^a z^a}_{\text{(i)}}
        + \underbrace{\sum_{a\ge2}\sum_{x=1}^{a-1} 2^{x+1} z^{a+1}}_{\text{(ii)}}
        + \underbrace{\sum_{a\ge2}\sum_{x=1}^{a-1}\sum_{t\ge2} 2^{x+1} z^{a+t}}_{\text{(iii)}} .$$
Using $\sum_{x=1}^{a-1} 2^{x+1} = 2^{a+1}-4$ and
$\sum_{t\ge2} z^{a+t} = z^{a+2}/(1-z)$:
$$ F(z) = \frac{2z}{1-2z}
        + \sum_{a\ge2}\bigl(2^{a+1}-4\bigr)\Bigl(z^{a+1} + \frac{z^{a+2}}{1-z}\Bigr)
        = \frac{2z}{1-2z} + \frac{1}{1-z}\sum_{b\ge3}\bigl(2^{b}-4\bigr) z^{b}, $$
and $\sum_{b\ge3}(2^b-4)z^b = \dfrac{8z^3}{1-2z} - \dfrac{4z^3}{1-z}$, so
$$ F(z) = \frac{2z}{1-2z} + \frac{8z^3}{(1-z)(1-2z)} - \frac{4z^3}{(1-z)^2}. $$

**Assembling** (rational-function algebra, machine-verified symbolically and by
coefficients against brute-force component sums for $m \le 11$ — Section 10, V6):
$$ A(z) = \tfrac12\, F(z)\,\frac{1-z}{1-3z}
        = \frac{z\,(1 - 2z + 3z^2)}{(1-z)(1-2z)(1-3z)}
        = \frac{3z}{1-3z} - \frac{3z}{1-2z} + \frac{z}{1-z}. $$

**Theorem 8.** For all $n \ge 1$:
$$ a_n = [z^n]A(z) = 3\cdot 3^{n-1} - 3\cdot 2^{n-1} + 1 = 3^n - 3\cdot2^{n-1} + 1, $$
and, since $(1-6z+11z^2-6z^3)A(z) = z - 2z^2 + 3z^3$ is a polynomial of degree 3,
$$ a_n = 6a_{n-1} - 11a_{n-2} + 6a_{n-3} \quad (n\ge4), \qquad a_1=1,\ a_2=4,\ a_3=16.\ \square $$

---

## 8. The transfer matrix / finite automaton formulation

The structure proved above is exactly a weighted regular language, which yields the
transfer matrix demanded by the strategy. Encode each shape $s$ with
$\mathrm{Sol}(E(s)) \neq \emptyset$ by a **role word** $\rho(s) \in \{A,B,C,D,E\}^n$
(one letter per arc, in arc order), determined by the classification:

* first component of type (i) ($\mathrm U^a\mathrm D^a$): $A^a$;
* first component of type (ii)/(iii) (parameters $a, x, t$): $A^x\, B^{a-x}\, C^t$;
* each non-first component $\mathrm U(\mathrm{UD})^k \mathrm D$: $D\, E^k$.

By Lemmas 7a/7b, $s \mapsto \rho(s)$ is a bijection from nonzero shapes onto the regular
language
$$ L \;=\; A\,A^*\,\bigl(B\,B^*\,C\,C^*\bigr)?\ \bigl(D\,E^*\bigr)^* $$
(read off the parameter ranges: $\#A = x \ge 1$, $\#B = a-x \ge 1$ and $\#C = t \ge 1$
or both absent, etc.); the inverse reconstructs $(a, x, t)$ and the $k$'s from the block
lengths. Assign transition weights = number of free sign choices consumed:
the very first $A$ has weight 1 ($\varepsilon_1$ is immaterial), every later $A$ weight
2, the first $B$ of the $B$-block weight 2 (the choice of the common value $v$), later
$B$'s weight 1, $C$'s weight 1 (forced signs), each $D$ weight 2 (free sign of a
component's first arc), $E$'s weight 1 (forced). Then by Lemmas 6–7 the total weight of
$\rho(s)$ equals $\tfrac12|\mathrm{Sol}(E(s))|$, the number of avoiders of shape $s$:
for a type-(i) first component, $1\cdot 2^{a-1} = 2^a/2 = N/2$; for a type-(ii)/(iii)
first component, $1 \cdot 2^{x-1}\cdot 2 = 2^{x} = 2^{x+1}/2 = N/2$ (first $A$ weight 1,
remaining $x-1$ $A$'s weight 2, first $B$ weight 2); times $2$ per later component
($= M(c)$).

The language with these weights is computed by the deterministic automaton with states
$q_1$ ("inside the leading $A$-block"), $q_2$ ("inside the $B$-block"), $q_3$ ("inside
the $C$-block"), $q_4$ ("inside the trailing components"), start configuration "first
arc read, in $q_1$" and accepting set $\{q_1, q_3, q_4\}$ ($q_2$ is non-accepting: a
$B$-block must be followed by a $C$). The weighted transfer matrix is
$$ M = \begin{pmatrix} 2 & 2 & 0 & 2\\ 0 & 1 & 1 & 0\\ 0 & 0 & 1 & 2\\ 0 & 0 & 0 & 3 \end{pmatrix}
\qquad
\begin{aligned}
&q_1 \to q_1: A(2),\quad q_1\to q_2: B(2),\quad q_1 \to q_4: D(2),\\
&q_2 \to q_2: B(1),\quad q_2\to q_3: C(1),\\
&q_3 \to q_3: C(1),\quad q_3\to q_4: D(2),\\
&q_4 \to q_4: E(1) + D(2) = 3,
\end{aligned} $$
$$ a_n \;=\; e_1^{\mathsf T} M^{\,n-1} f, \qquad e_1 = (1,0,0,0)^{\mathsf T},\quad
   f = (1,0,1,1)^{\mathsf T}. $$
Its characteristic polynomial is $(\lambda-1)^2(\lambda-2)(\lambda-3)$ — the spectrum
$\{1,2,3\}$ predicted by the conjectured formula. The generating function
$z\, e_1^{\mathsf T}(I - zM)^{-1} f$ equals $A(z)$ of Section 7 (machine-verified
symbolically, V7), so this formulation independently re-derives Theorem 8; the factor
$(\lambda-1)^2$ cancels against the numerator, leaving the minimal recurrence
$a_n = 6a_{n-1} - 11a_{n-2} + 6a_{n-3}$.

*Sanity check by hand:* $n=1$: weight 1 (word $A$). $n=2$: $AA$ (2) $+\, AD$ (2) $= 4$.
$n=3$: $AAA$ (4) $+ AAD$ (4) $+ ABC$ (2) $+ ADD$ (4) $+ ADE$ (2) $= 16$. ✓

---

## 9. Worked example ($n = 4$)

Shape $s = \mathrm{UUUDDUDD}$: one irreducible component, $a = 3$, first D-run has
$x = 2$, $t = 1$: type (ii) with $N = 2^{x+1} = 8$, so $8/2 = 4$ avoiders — the data
shows exactly the four words $23123414,\ 23423141,\ 32132414,\ 32432141$, whose sign
vectors $(\varepsilon_2,\varepsilon_3,\varepsilon_4)$ are $(+,-,+), (+,+,-), (-,-,+),
(-,+,-)$: precisely the solutions of the single constraint
$\varepsilon_3 = -\varepsilon_4$ ($j=4$, $\beta_4 = 2$, range $\{3\}$).
Shape $\mathrm{UUDUUDDD}$: $j=3$ forces $\varepsilon_2 = -\varepsilon_3$, $j=4$
($\beta_4 = 1$) forces $\varepsilon_2 = \varepsilon_3 = -\varepsilon_4$: contradiction, 0
avoiders — matching the data.

---

## 10. Numeric validation log

Ground truth: `../data/refined_stats.json` (Rust enumerator `enumerator.rs`, bitwise
identical to `enumerator.py` for $n\le7$, plus a clean-room Codex implementation; see
`../data/validation.json`), which records the avoider count **per Dyck shape** for all
$n \le 8$. Verification drivers (this work):
`../data/verify_characterization.py`, `../data/verify_gf.py`
(log: `../data/verify_characterization_n7.log`). All checks **passed**:

| # | Claim tested | Range tested | Method |
|---|---|---|---|
| V1 | Lemma 2: avoidance $\iff$ P1$\wedge$P2 | every $(s,p)$, $n\le7$ (2,162,160 pairs at $n=7$) | literal P1/P2 vs fast avoidance check (itself validated against the naive 4-index definition, see `enumerator.py` V1) |
| V2 | Lemma 3: Av(132,312) = prefix-extremal, sign bijection roundtrip, count $2^{n-1}$ | $n\le8$ | exhaustive |
| V3 | Lemma 4 + Theorem 5: P2 $\iff E(s)$; full set equality avoiders $=$ image of $\{(s,\varepsilon)\}$ | every $(s,p)$ with P1, $n\le7$; set equality $n\le7$ | exhaustive |
| V4 | Lemma 6: $|\mathrm{Sol}(E(s))| = N(c^{(1)})\prod M(c^{(\ell)})$ | every Dyck shape, $n\le8$ | brute solution count vs product of brute component counts |
| V5 | Lemmas 7a/7b: closed forms for $M(c), N(c)$; per-shape counts vs Rust ground truth | every irreducible $c$ with $\le8$ arcs; every shape $n\le8$ (incl. all zero shapes) | brute vs formula vs `refined_stats.json` |
| V6 | Section 7: $[z^m]F = \sum_c N(c)$, $[z^m]G = \sum_c M(c)$; the two geometric-series identities; $A = \frac12 F\frac{1-z}{1-3z} = \frac{3z}{1-3z}-\frac{3z}{1-2z}+\frac{z}{1-z}$; $(1-6z+11z^2-6z^3)A = z-2z^2+3z^3$ | components to $m\le11$; identities symbolic (sympy) + coefficients to $z^{24}$ | sympy + brute |
| V7 | Section 8: $e_1^{\mathsf T}M^{n-1}f = 3^n-3\cdot2^{n-1}+1$; $z e_1^{\mathsf T}(I-zM)^{-1}f = A(z)$; charpoly $=(\lambda-1)^2(\lambda-2)(\lambda-3)$ | $n\le40$; symbolic | exact integer arithmetic + sympy |
| V8 | Recurrence $a_n = 6a_{n-1}-11a_{n-2}+6a_{n-3}$ on formula values | $4\le n\le40$ | exact |

Independent prior ground truth (not produced by this proof effort): $a_n$ matches
$3^n - 3\cdot2^{n-1}+1$ for $n = 1..8$ ($1, 4, 16, 58, 196, 634, 1996, 6178$) by three
independent enumerators (`../data/counts.json`, `../data/validation.json`).

---

## 11. Status, gaps, remarks

**Status: complete proof; no known gaps.**

**Hostile-referee pass (Codex GPT-5.5, xhigh, thread
`019eb9c1-1e41-7b81-a2be-207514f1c365`, June 2026):** audited every lemma proof
case-by-case and ran its own clean-room implementations written from the draft's
statements (not from this project's scripts): exact avoider-set equality of Theorem 5's
characterization for $n\le7$ (all 2,162,160 nonnesting words at $n=7$), Lemma 2
equivalence through $n=6$, component formulas against brute sign-system counts for every
Dyck shape through $n=8$, and symbolic reduction of both the Section 7 GF and the Section
8 transfer matrix to $z(1-2z+3z^2)/((1-z)(1-2z)(1-3z))$. Verdict: "CONFIRMED — no gaps
found", after one **cosmetic** arithmetic typo in Section 8's prose weight bookkeeping
was found and fixed (the fix was re-confirmed, including the $x=1$ edge).

Every step is an explicit finite argument:

1. Lemma 1 (normal form) — proved, both directions explicit.
2. Lemma 2 (P1/P2 characterization) — proved by exhaustive case analysis on the five
   endpoint configurations; both directions.
3. Lemma 3 (sign bijection) — proved by induction with explicit inverse.
4. Lemma 4 (P2 $\iff E(s)$ given P1) — proved; uses $\beta_j \ge 1$ essentially (the
   constraint deactivates before the first closer, which is what makes first components
   freer than later ones).
5. Lemma 6 (factorization) — proved by index translation.
6. Lemmas 7a/7b (component classification) — proved; the "minimal bad $j$" arguments are
   self-contained.
7. Section 7 algebra — formal power series manipulations, machine-checked.
8. Section 8 — equivalent automaton formulation; spectrum $\{1, 2, 3\}$ as demanded by
   the strategy (the $(\lambda-1)^2$ is an artifact of the 4-state presentation and
   cancels in the generating function).

Honest caveats for the referee:

* The five-case analysis in Lemma 2 and the index bookkeeping in Lemmas 4–7 are the
  places where an error would hide; this is why V1–V5 test exactly these statements
  exhaustively (not just the final counts) through $n=7$/$n=8$ against independently
  produced ground truth.
* Lemma 4 is stated and used only for prefix-extremal $p$ (P1 holders); P2 alone is
  **not** equivalent to $E(s)$ on general $p$, and the proof never needs that.
* The counting convention (raw words, biconditional containment) is the paper's;
  both are pinned in DEFINITIONS.md and hard-coded in the validated enumerators.
* For Lean formalization: Lemmas 1–4 are statements about finite words with explicit
  maps; Lemma 6/7 are statements about finite constraint systems; Section 7 can be
  bypassed entirely in Lean by proving the recurrence directly from the weighted-DFA
  formulation of Section 8 (a 4-dimensional linear recurrence with integer entries),
  which avoids formal power series.
