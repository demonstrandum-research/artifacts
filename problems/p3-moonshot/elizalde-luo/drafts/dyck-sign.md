# A proof of the Elizalde–Luo conjecture for $\{1132, 3312\}$ via Dyck shapes and sign words

**Status: complete proof draft (no known gaps). All lemmas verified numerically; see the
validation log in Section 9.**

**Conjecture (Elizalde–Luo, arXiv:2412.00336, DMTCS 27:1 (2025), Table 4).**
The number of nonnesting permutations of the multiset $[n]_2=\{1,1,2,2,\dots,n,n\}$ that
avoid the patterns $1132$ and $3312$ equals
$$ 3^n - 3\cdot 2^{n-1} + 1 \qquad (n \ge 1). $$

All conventions (containment with biconditional equality, nonnesting via $1221/2112$,
raw-word counting) are exactly those pinned in `../DEFINITIONS.md`, quoted verbatim from
the published paper.

---

## 0. Conventions and notation

A *word* is $w = w_1 w_2 \cdots w_{2n}$ over $\{1,\dots,n\}$ using each letter exactly
twice (a permutation of $[n]_2$). Positions are $1$-based.

**Containment.** $w$ contains a pattern $\sigma = \sigma_1\cdots\sigma_k$ if there are
positions $i_1 < \cdots < i_k$ with, for all $r,s$:
$w_{i_r} < w_{i_s} \iff \sigma_r < \sigma_s$ and $w_{i_r} = w_{i_s} \iff \sigma_r =
\sigma_s$. Otherwise $w$ avoids $\sigma$.

**Nonnesting.** $w$ is *nonnesting* if it avoids $1221$ and $2112$.

For each value $v$ let $\mathrm{fst}(v) < \mathrm{snd}(v)$ be the positions of its two
occurrences; the *arc* of $v$ is the pair $(\mathrm{fst}(v), \mathrm{snd}(v))$. A
position is an *opener* if it is the first occurrence of its value, a *closer*
otherwise. Two arcs *nest* if one lies strictly inside the other:
$\mathrm{fst}(u) < \mathrm{fst}(v) < \mathrm{snd}(v) < \mathrm{snd}(u)$.

An *avoider* is a nonnesting word avoiding both $1132$ and $3312$. Write $c_n$ for the
number of avoiders. The goal is $c_n = 3^n - 3\cdot 2^{n-1}+1$.

---

## 1. Lemma 0: nonnesting words = (Dyck shape) $\times$ (label permutation)

Let $s \in \{U,D\}^{2n}$ be a *Dyck word*: $n$ letters $U$, $n$ letters $D$, every
prefix containing at least as many $U$ as $D$. Let $o_1 < \cdots < o_n$ be the positions
of the $U$'s and $q_1 < \cdots < q_n$ those of the $D$'s.

**Fact 0.1.** In a Dyck word, $o_i < q_i$ for all $i$.
*Proof.* The prefix ending at $q_i$ contains $i$ letters $D$, hence at least $i$
letters $U$; the $i$-th $U$ therefore occurs at a position $< q_i$. $\square$

For a Dyck word $s$ and a permutation $p = (p_1,\dots,p_n)$ of $[n]$ define the word
$\mathrm{wd}(s,p)$ by placing $p_i$ at position $o_i$ and at position $q_i$.

**Lemma 0.** A word $w$ (permutation of $[n]_2$) is nonnesting if and only if
$w = \mathrm{wd}(s,p)$ for a (unique) Dyck word $s$ and permutation $p$. Here $s$ is the
opener/closer indicator of $w$ ($U$ at first occurrences, $D$ at second occurrences) and
$p_i$ is the value at the $i$-th opener.

*Proof.* **Step 1: $w$ contains $1221$ or $2112$ $\iff$ two arcs of $w$ nest.**
An occurrence $i_1<i_2<i_3<i_4$ of $1221$ has $w_{i_1}=w_{i_4}=:u$ and
$w_{i_2}=w_{i_3}=:v$ with $u<v$ (equal pattern letters force equal values, and each
value occurs exactly twice, so $\{i_1,i_4\}$ are the two occurrences of $u$ and
$\{i_2,i_3\}$ those of $v$). Thus $w$ contains $1221$ iff there are values $u<v$ with
$\mathrm{fst}(u)<\mathrm{fst}(v)<\mathrm{snd}(v)<\mathrm{snd}(u)$, i.e. the arc of $v$
nested inside the arc of $u$ with $u < v$. Symmetrically, $w$ contains $2112$ iff there
are values $u>v$ with the arc of $v$ nested inside that of $u$. Avoiding both is
equivalent to: no two arcs nest.

**Step 2: no two arcs nest $\iff$ openers and closers are matched in the same order.**
($\Leftarrow$) If for all values $u \ne v$, $\mathrm{fst}(u)<\mathrm{fst}(v)$ implies
$\mathrm{snd}(u)<\mathrm{snd}(v)$, no nesting is possible. ($\Rightarrow$) If
$\mathrm{fst}(u)<\mathrm{fst}(v)$ and $\mathrm{snd}(v)<\mathrm{snd}(u)$ then, using
$\mathrm{fst}(v)<\mathrm{snd}(v)$, the arcs nest. So nonnesting is equivalent to: the
order of values by first occurrence equals their order by second occurrence. Sorting
values by first occurrence as $v_1, \dots, v_n$, this says the $i$-th closer carries the
value $v_i$ of the $i$-th opener.

**Step 3: the bijection.** Given nonnesting $w$, let $s$ be its opener/closer indicator.
Every prefix of $w$ contains at least as many openers as closers (each closer's opener
precedes it), so $s$ is a Dyck word. Let $p_i$ be the value at the $i$-th opener; by
Step 2 the $i$-th closer also carries $p_i$, hence $w = \mathrm{wd}(s,p)$. Conversely,
for any Dyck $s$ and permutation $p$, in $\mathrm{wd}(s,p)$ the $i$-th $U$-position is
the first occurrence of $p_i$: any earlier position carries either $p_j$ ($j<i$, an
earlier $U$) or $p_j$ for an earlier $D$, and the $j$-th $D$ is preceded by at least $j$
$U$'s, so $j \le i-1$; either way the value differs from $p_i$. By Fact 0.1, $o_i <
q_i$, so the value $p_i$ has its arc $(o_i, q_i)$; arcs are simultaneously sorted by
opener and by closer, so no two nest, and $\mathrm{wd}(s,p)$ is nonnesting by Steps 1–2.
The two constructions are mutually inverse by definition. $\square$

From now on we identify a nonnesting word with its pair $(s,p)$ and freely use:
*arc $i$* has opener $o_i$, closer $q_i$, value $p_i$. We say arc $K$ is **open at
position $t$** if $o_K < t < q_K$ (equivalently $o_K < t$ and $q_K > t$; we only use
this with $t$ an opener position $o_J$, $J\neq K$, so ties do not occur), and write
$$\mathrm{open}(t) = \{K : o_K < t < q_K\}.$$
The *height* of $s$ after $t$ steps is $h_t = \#\{U\text{'s among } s_1..s_t\} -
\#\{D\text{'s among } s_1..s_t\} = |\{K: o_K \le t < q_K\}|$; in particular the number
of arcs open at an opener position $o_J$ is $h_{o_J - 1}$, the height from which that
$U$-step starts.

---

## 2. Lemma 1: a positional criterion for containing 1132 / 3312

**Lemma 1.** Let $w$ be a permutation of $[n]_2$.
1. $w$ contains $1132$ $\iff$ there exist a value $v$ and positions
   $t < t'$, both $> \mathrm{snd}(v)$, with $w_t > w_{t'} > v$.
2. $w$ contains $3312$ $\iff$ there exist a value $v$ and positions
   $t < t'$, both $> \mathrm{snd}(v)$, with $w_t < w_{t'} < v$.

*Proof.* (1, $\Leftarrow$) Take positions $i_1=\mathrm{fst}(v) < i_2=\mathrm{snd}(v) <
t < t'$ and the subsequence $(v, v, w_t, w_{t'})$. Compare with $\sigma = 1132$:
equalities — $\sigma_1=\sigma_2$ and $w_{i_1}=w_{i_2}$; all other pairs of pattern
letters are distinct, and correspondingly $w_t \ne w_{t'}$, $w_t \ne v$, $w_{t'} \ne v$
(all strict inequalities hold by hypothesis). Order relations — $\sigma$ requires
$1 < 2 < 3$, i.e. $v < w_{t'} < w_t$, which is the hypothesis. So this is an occurrence.

(1, $\Rightarrow$) Let $i_1<i_2<i_3<i_4$ be an occurrence of $1132$. Then
$w_{i_1} = w_{i_2} =: v$; since $v$ occurs exactly twice, $i_2 = \mathrm{snd}(v)$.
The pattern forces $w_{i_3} > w_{i_4} > v$ with $i_3 < i_4$ both $> \mathrm{snd}(v)$:
take $t = i_3$, $t' = i_4$.

(2) Identical with all inequalities reversed: an occurrence of $3312$ is
$(v, v, w_t, w_{t'})$ with $w_t < w_{t'} < v$ and $t<t'$ after $\mathrm{snd}(v)$.
$\square$

**Corollary 1.1 (the $\star$-conditions).** A nonnesting word $(s,p)$ is an avoider iff
for every $i \in [n]$ there is **no** pair of positions $t<t'$, both $>q_i$, with

- ($\mathrm{D}_i$, "descent above $p_i$"): $\;w_t > w_{t'} > p_i$, nor
- ($\mathrm{A}_i$, "ascent below $p_i$"): $\;w_t < w_{t'} < p_i$.

*Proof.* Immediate from Lemma 1, since $\mathrm{snd}(p_i) = q_i$ by Lemma 0. $\square$

---

## 3. Lemma 2: avoiders have prefix-interval labels; the sign word $\varepsilon$

Call $p \in S_n$ **prefix-interval** if for every $j$, the set $\{p_1,\dots,p_j\}$ is an
interval of integers. Equivalently: for each $j \ge 2$, $p_j = \min\{p_1..p_{j-1}\}-1$
(write $\varepsilon_j = \mathsf{L}$) or $p_j = \max\{p_1..p_{j-1}\}+1$ (write
$\varepsilon_j = \mathsf{H}$). The word $\varepsilon = (\varepsilon_2, \dots,
\varepsilon_n) \in \{\mathsf{L},\mathsf{H}\}^{n-1}$ is the **sign word** of $p$.

**Fact 2.1 (bijection).** $p \mapsto \varepsilon$ is a bijection from prefix-interval
permutations of $[n]$ onto $\{\mathsf{L},\mathsf{H}\}^{n-1}$.
*Proof.* Given $\varepsilon$, the reconstruction is forced: $\{p_1..p_n\} = [n]$ and the
$\mathsf{L}$-steps go below $p_1$, the $\mathsf{H}$-steps above, so
$p_1 = 1 + \#\{j : \varepsilon_j = \mathsf{L}\}$, and then each $p_j$ is determined
($\mathsf{L}$: current min $-1$; $\mathsf{H}$: current max $+1$). This always produces a
permutation of $[n]$, and the two maps are mutually inverse. $\square$

**Fact 2.2 (comparison rule).** If $p$ is prefix-interval with sign word $\varepsilon$,
then for all $1 \le u < v \le n$:
$$ p_u < p_v \iff \varepsilon_v = \mathsf{H}, \qquad p_u > p_v \iff \varepsilon_v = \mathsf{L}. $$
*Proof.* If $\varepsilon_v = \mathsf{H}$ then $p_v = \max\{p_1..p_{v-1}\}+1 > p_u$;
if $\varepsilon_v = \mathsf{L}$ then $p_v = \min\{p_1..p_{v-1}\}-1 < p_u$. These two
cases are exhaustive and exclusive. $\square$

**Lemma 2.** If $(s,p)$ is an avoider then $p$ is prefix-interval.

*Proof.* Suppose not; let $j$ be minimal with $\{p_1..p_j\}$ not an interval. Then
$j \ge 2$, $I := \{p_1..p_{j-1}\}$ is an interval $[lo, hi]$, and $p_j \notin
[lo-1, hi+1]$ (note $p_j \notin I$). Two cases.

*Case $p_j \ge hi+2$.* Let $h := p_j - 1$. Then $hi < h < p_j$, so $h \notin I \cup
\{p_j\}$, hence $h = p_m$ for some $m > j$. Consider the positions
$q_1 < q_j < q_m$ (closers are increasing in the arc index, and $1 < j < m$). At these:
$w_{q_j} = p_j$, $w_{q_m} = h$, and $p_j > h > hi \ge p_1$. So $t=q_j < t'=q_m$, both
$> q_1$, with $w_t > w_{t'} > p_1$: condition ($\mathrm{D}_1$) of Corollary 1.1 is
violated — $w$ contains $1132$. Contradiction.

*Case $p_j \le lo-2$.* Let $h := p_j + 1 < lo$; as above $h = p_m$ with $m > j$. Then
$t = q_j < t' = q_m$, both $> q_1$, with $w_t = p_j < w_{t'} = h < lo \le p_1$:
condition ($\mathrm{A}_1$) is violated — $w$ contains $3312$. Contradiction. $\square$

*Remark.* Prefix-interval permutations are exactly the classical
$\{132,312\}$-avoiding permutations; we do not need this fact.

---

## 4. Theorem A: the structural characterization

Fix a Dyck word $s$ with openers $o_1<\dots<o_n$, closers $q_1<\dots<q_n$. Let
$a = a(s) \ge 1$ be the length of the first ascent of $s$ (the number of $U$'s before
the first $D$, so $q_1 = a+1$ and arcs $1,\dots,a$ are exactly those with $o_K < q_1$).
Call arc $J$ **late** if $o_J > q_1$, i.e. $J \ge a+1$; otherwise **early**.

**Observation 4.1.** If $J$ is late, then $1 \notin \mathrm{open}(o_J)$, and every
$K \in \mathrm{open}(o_J)$ satisfies $2 \le K < J$.
*Proof.* $K \in \mathrm{open}(o_J)$ gives $o_K < o_J$, so $K < J$; and $K = 1$ would
need $q_1 > o_J$, contradicting lateness. $\square$

**Theorem A.** A pair $(s,p)$ is an avoider if and only if

1. $p$ is prefix-interval, with sign word $\varepsilon$; and
2. for every late arc $J$ and every $K \in \mathrm{open}(o_J)$:
   $\varepsilon_K \neq \varepsilon_J$.

*Proof.*

**($\Rightarrow$).** Let $(s,p)$ be an avoider. Condition 1 is Lemma 2. For
condition 2, let $J$ be late and $K \in \mathrm{open}(o_J)$; by Observation 4.1,
$2 \le K < J$. Suppose $\varepsilon_K = \varepsilon_J = \mathsf{H}$. By Fact 2.2,
$p_J > p_K$ (from $\varepsilon_J = \mathsf{H}$, $K<J$) and $p_K > p_1$ (from
$\varepsilon_K = \mathsf{H}$, $1<K$). Take $t = o_J$ and $t' = q_K$. Then
$t < t'$ (openness: $o_J < q_K$), both exceed $q_1$ (lateness: $o_J > q_1$; and
$q_K > o_J > q_1$), and $w_t = p_J > w_{t'} = p_K > p_1$. This violates
($\mathrm{D}_1$), so $w$ contains $1132$ — contradiction. If instead
$\varepsilon_K = \varepsilon_J = \mathsf{L}$, Fact 2.2 gives $p_J < p_K < p_1$ and the
same positions violate ($\mathrm{A}_1$), producing $3312$ — contradiction.

**($\Leftarrow$).** Let $(s,p)$ satisfy 1 and 2, and suppose $(s,p)$ is not an avoider.
By Corollary 1.1, some condition ($\mathrm{D}_i$) or ($\mathrm{A}_i$) is violated.

*Case ($\mathrm{D}_i$):* there are $t<t'$, both $>q_i$, with $w_t > w_{t'} > p_i$. Let
$A$ and $B$ be the arcs of positions $t$, $t'$ respectively; $A \ne B$ since
$w_t \ne w_{t'}$. Every arc $C \le i$ has both positions $\le q_i$ (indeed
$o_C < q_C \le q_i$), so $A > i$ and $B > i$. Now:

- $p_B > p_i$ with $i < B$ forces $\varepsilon_B = \mathsf{H}$ (Fact 2.2).
- If $A < B$, then $\varepsilon_B = \mathsf{H}$ gives $p_A < p_B$, contradicting
  $w_t = p_A > p_B = w_{t'}$. Hence $B < A$.
- $p_A > p_B$ with $B < A$ forces $\varepsilon_A = \mathsf{H}$.
- Positions: $t \in \{o_A, q_A\}$ and $t' \in \{o_B, q_B\}$ with $t < t'$. Since
  $B < A$ we have $o_B < o_A$ and $q_B < q_A$. If $t = q_A$, then $t' > q_A$, but both
  positions of $B$ are $< q_A$ — impossible. So $t = o_A$; then $t' = o_B$ is impossible
  ($o_B < o_A$), so $t' = q_B$ and $o_A < q_B$. Together with $o_B < o_A$ this says
  $B \in \mathrm{open}(o_A)$.
- $A$ is late: $o_A = t > q_i \ge q_1$.

So $A$ is late, $B \in \mathrm{open}(o_A)$, and $\varepsilon_B = \varepsilon_A =
\mathsf{H}$ — contradicting condition 2.

*Case ($\mathrm{A}_i$):* there are $t<t'$, both $>q_i$, with $w_t < w_{t'} < p_i$. Let
$A, B$ be the arcs of $t, t'$; as before $A \ne B$ and $A, B > i$ (arcs $\le i$ have
both positions $\le q_i$). Now:

- $p_B < p_i$ with $i < B$ forces $\varepsilon_B = \mathsf{L}$ (Fact 2.2).
- If $A < B$, then $\varepsilon_B = \mathsf{L}$ gives $p_A > p_B$, contradicting
  $w_t = p_A < p_B = w_{t'}$. Hence $B < A$.
- $p_A < p_B$ with $B < A$ forces $\varepsilon_A = \mathsf{L}$.
- Positions: exactly as in case ($\mathrm{D}_i$) — $B < A$ gives $o_B < o_A$ and
  $q_B < q_A$; $t = q_A$ is impossible (both positions of $B$ precede $q_A$), so
  $t = o_A$; $t' = o_B$ is impossible ($o_B < o_A$), so $t' = q_B$ with $o_A < q_B$,
  i.e. $B \in \mathrm{open}(o_A)$.
- $A$ is late: $o_A = t > q_i \ge q_1$.

So $\varepsilon_B = \varepsilon_A = \mathsf{L}$ with $A$ late and
$B \in \mathrm{open}(o_A)$ — contradicting condition 2. $\square$

**Corollary A.1.** For each Dyck word $s$, the number of avoiders with shape $s$ is
$$ N(s) \;=\; \#\bigl\{\varepsilon \in \{\mathsf{L},\mathsf{H}\}^{n-1} \;:\;
\varepsilon_J \ne \varepsilon_K \text{ for every late } J \text{ and }
K \in \mathrm{open}(o_J)\bigr\}, $$
and $c_n = \sum_{s} N(s)$ over all Dyck words of semilength $n$.
*Proof.* Theorem A plus Fact 2.1 (bijection $p \leftrightarrow \varepsilon$) plus
Lemma 0 (avoiders $\leftrightarrow$ pairs $(s,p)$). $\square$

We call an $\varepsilon$ satisfying the displayed condition **valid for $s$**.

---

## 5. Lemma B: classification of shapes and the per-shape count

Fix $s$ with first ascent $a$. Call an opener position a **gap opener** if it lies
strictly between $q_1$ and $q_a$ (if $a = 1$ this interval is empty). Note every gap
opener belongs to a late arc, and arcs $1..a$ have $o_K \le a < q_1$.

**Observation 5.0.** (i) The closers $q_1 < \dots < q_a$ all lie in $[q_1, q_a]$ and
the closers of late arcs all lie after $q_a$: if any late arc exists then $a < n$, and
every late arc $J \ge a+1$ has $q_J \ge q_{a+1} > q_a$. (ii) For a
position $t$ with $q_a < t$: every arc open at $t$ is late (an early arc $K \le a$ has
$q_K \le q_a < t$). (iii) Arc $a \in \mathrm{open}(t)$ for every $t$ with
$q_1 < t < q_a$, provided $a \ge 2$ (indeed $o_a \le a < q_1 < t < q_a$).

**Classification.** Exactly one of the following holds for $s$:

- **Form (i):** no gap openers, and every opener after $q_a$ starts at height $\le 1$.
  Then $s = U^a D^a\, T$ where $T$ (the part after $q_a$) is a path from height $0$ to
  $0$, never negative, in which every $U$ starts at height $\le 1$.
- **Form (ii):** exactly one gap opener, and every opener after $q_a$ starts at height
  $\le 1$. Writing $i \in \{1,\dots,a-1\}$ for the number of closers before the gap
  opener, $s = U^a D^i\, U\, D^{a-i}\, T$ where $T$ is a path from height $1$ to $0$,
  never negative, in which every $U$ starts at height $\le 1$. The gap opener is arc
  $B := a+1$.
- **Form (z):** at least two gap openers, or some opener after $q_a$ starts at height
  $\ge 2$.

*Proof of the shape descriptions.* If there are no gap openers, positions
$q_1, \dots, q_a$ are consecutive (all positions in $(q_1, q_a)$ are closers), so the
word starts $U^a D^a$ and $T$ := the remainder starts and ends at height $0$. If there
is exactly one gap opener at a position with $i$ closers before it, then $1 \le i$
(it is after $q_1$) and $i \le a-1$ (before $q_a$), all other positions in
$(q_1, q_a)$ are closers, giving $U^a D^i U D^{a-i}$; the gap opener is the
$(a{+}1)$-st opener, i.e. arc $a+1$; after $q_a$ the height is $1$ (exactly arc $B$ is
open, by Observation 5.0(i)+(ii): early arcs closed, $q_B = q_{a+1} > q_a$). In both
forms, "every $U$ of $T$ starts at height $\le 1$" restates the height condition.
Heights inside $T$ equal the number of open arcs, all late by 5.0(ii). $\square$

**Lemma B.** Let $u_0(T)$ denote the number of $U$-steps of $T$ starting at height $0$.
$$ N(s) = \begin{cases}
2^{\,(a-1) + u_0(T)} & \text{form (i)},\\[2pt]
2^{\,i + u_0(T)} & \text{form (ii)},\\[2pt]
0 & \text{form (z)}.
\end{cases} $$

*Proof.* Throughout, the constraints on $\varepsilon$ are exactly those of
Corollary A.1: one constraint set per late opener $J$, namely
$\varepsilon_J \notin \{\varepsilon_K : K \in \mathrm{open}(o_J)\}$; arcs in
$\mathrm{open}(o_J)$ have index in $\{2,\dots,J-1\}$ (Observation 4.1), so all
referenced coordinates of $\varepsilon$ exist.

**Form (z), two gap openers.** Then $a \ge 2$. Let $\beta < \beta'$ be the arcs of the
first two gap openers; both are late, with $q_1 < o_\beta < o_{\beta'} < q_a$. Suppose
$\varepsilon$ is valid. Arc $a$ is open at $o_\beta$ and at $o_{\beta'}$
(Observation 5.0(iii)), and arc $\beta$ is open at $o_{\beta'}$ (as
$o_\beta < o_{\beta'}$ and $q_\beta \ge q_{a+1} > q_a > o_{\beta'}$). Validity at
$o_\beta$ gives $\varepsilon_\beta \ne \varepsilon_a$, so
$\{\varepsilon_a, \varepsilon_\beta\} = \{\mathsf{L},\mathsf{H}\}$. Validity at
$o_{\beta'}$ needs $\varepsilon_{\beta'} \notin \{\varepsilon_a, \varepsilon_\beta\}$
— impossible. So $N(s) = 0$.

**Form (z), an opener after $q_a$ at height $\ge 2$.** Let $J$ be such an opener's arc:
$o_J > q_a$ and $|\mathrm{open}(o_J)| = h_{o_J - 1} \ge 2$. By Observation 5.0(ii) all
arcs of $\mathrm{open}(o_J)$ are late. Pick $C < C'$ in $\mathrm{open}(o_J)$. Then $C$
is open at $o_{C'}$ (indeed $o_C < o_{C'}$ since $C<C'$, and $q_C > o_J > o_{C'}$),
and $C'$ is late, so validity at $o_{C'}$ gives $\varepsilon_{C'} \ne \varepsilon_C$.
Validity at $o_J$ needs $\varepsilon_J \notin \{\varepsilon_C, \varepsilon_{C'}\} =
\{\mathsf{L},\mathsf{H}\}$ — impossible. So $N(s) = 0$.

**Form (i).** The late arcs are exactly the arcs of $T$'s $U$-steps. For a late $J$,
$\mathrm{open}(o_J)$ consists of late arcs only (5.0(ii)), and $|\mathrm{open}(o_J)| =$
height of $T$ before that $U$-step, which is $0$ or $1$ by hypothesis. So the
constraints are: at each $T$-opener at height $1$, $\varepsilon_J \ne \varepsilon_Z$
where $Z = Z(J)$ is the unique open arc at $o_J$ (note $Z$ is itself a late arc, i.e. an
earlier $T$-opener); at each $T$-opener at height $0$, no constraint; the coordinates
$\varepsilon_2, \dots, \varepsilon_a$ are unconstrained.

Let $F$ = $\{2,\dots,a\} \cup \{$arcs of $T$-openers at height $0\}$, so
$|F| = (a-1) + u_0(T)$. The restriction map $\varepsilon \mapsto \varepsilon|_F$ is a
bijection from valid sign words onto $\{\mathsf{L},\mathsf{H}\}^F$:

- *Injectivity and well-definedness of the inverse:* process the late openers in
  position order. At a height-$0$ opener, $\varepsilon_J$ is the prescribed free value.
  At a height-$1$ opener, $Z(J)$ is an earlier-processed arc (or in form (ii) below,
  possibly $B$), so $\varepsilon_{Z(J)}$ is already determined and
  $\varepsilon_J$ is forced to its opposite — exactly one choice. Hence each element of
  $\{\mathsf{L},\mathsf{H}\}^F$ extends to exactly one constraint-respecting
  $\varepsilon$.
- *Validity of the extension:* every constraint of Corollary A.1 is of the form handled
  (late openers in form (i) see $0$ or $1$ open arcs), and each is satisfied by
  construction.

Hence $N(s) = 2^{|F|} = 2^{(a-1)+u_0(T)}$.

**Form (ii).** The late arcs are $B = a+1$ and the arcs of $T$'s $U$-steps. We compute
$\mathrm{open}(o_B)$: early arcs $K$ with $q_K > o_B$ are exactly $K \in
\{i+1, \dots, a\}$ (the closers before $o_B$ are precisely $q_1, \dots, q_i$); no late
arc is open at $o_B$ (late openers other than $o_B$ lie after $q_a > o_B$). So
$\mathrm{open}(o_B) = \{i+1, \dots, a\}$, of size $a - i \ge 1$. For $T$-openers, as in
form (i), $\mathrm{open}(o_J)$ has size $0$ or $1$ and consists of late arcs (which now
include $B$).

A sign word is valid iff: (1) $\varepsilon_B \ne \varepsilon_K$ for all
$K \in \{i+1..a\}$ — since $\varepsilon_B$ takes one of two values, this holds iff
$\varepsilon_{i+1} = \cdots = \varepsilon_a =: x$ **and** $\varepsilon_B = \bar{x}$
(if $\varepsilon$ is not constant on $\{i+1..a\}$, both letters appear among the
forbidden values and no $\varepsilon_B$ exists); and (2) the same height-$0$/height-$1$
conditions on $T$-openers as in form (i).

Let $F = \{2,\dots,i\} \cup \{a\} \cup \{$arcs of $T$-openers at height $0\}$ — i.e.
free coordinates: $\varepsilon_2..\varepsilon_i$ free, the common value
$x = \varepsilon_a$ free, height-$0$ $T$-arcs free; forced: $\varepsilon_{i+1} = \cdots
= \varepsilon_{a-1} = x$, $\varepsilon_B = \bar x$, height-$1$ $T$-arcs as in form (i).
The same processing argument shows restriction to $F$ is a bijection onto
$\{\mathsf{L},\mathsf{H}\}^F$, so
$N(s) = 2^{|F|} = 2^{(i-1) + 1 + u_0(T)} = 2^{i + u_0(T)}$. $\square$

---

## 6. Lemma C: two weighted path counts

For $m \ge 0$ let $\mathcal{P}_0(m)$ (resp. $\mathcal{P}_1(m)$) be the set of
$\{U,D\}$-paths from height $0$ (resp. height $1$) to height $0$, never negative, with
exactly $m$ $U$-steps (hence $m$, resp. $m+1$, $D$-steps), such that every $U$ starts at
height $\le 1$. Define the weighted counts
$$ A_m = \sum_{T \in \mathcal{P}_0(m)} 2^{u_0(T)}, \qquad
   B_m = \sum_{T \in \mathcal{P}_1(m)} 2^{u_0(T)}, $$
with $u_0(T)$ = number of $U$-steps starting at height $0$.

**Lemma C.** $A_0 = B_0 = 1$; for $m \ge 1$: $B_m = 3^m$ and $A_m = 2 \cdot 3^{m-1}$.

*Proof.* $\mathcal{P}_0(0) = \{\text{empty path}\}$ and $\mathcal{P}_1(0) = \{D\}$, each
of weight $1$.

For $m \ge 1$, classify by the first step.

*$A$-recurrence:* a nonempty path from height $0$ must start with $U$ (a $D$ would go
negative), starting at height $0$: weight factor $2$. The remainder is a path from
height $1$ to $0$ with $m-1$ $U$'s, all $U$'s starting at height $\le 1$ (heights in the
remainder are heights in $T$). Conversely each such remainder yields a path of
$\mathcal{P}_0(m)$. The weight multiplies: $u_0(T) = 1 + u_0'$ where $u_0'$ counts
height-$0$ $U$'s of the remainder (the remainder's steps occur at the same absolute
heights). Hence $A_m = 2 B_{m-1}$.

*$B$-recurrence:* a path of $\mathcal{P}_1(m)$, $m \ge 1$, starts with $U$ or $D$.
  - First step $D$: the remainder is in $\mathcal{P}_0(m)$ with equal weight:
    contribution $A_m$.
  - First step $U$ (from height $1$: weight factor $1$): the path reaches height $2$;
    a next step exists (the path is at height $2$ and must end at height $0$) and it
    cannot be $U$ (a $U$ from height $2$ is forbidden), so it is $D$, returning to
    height $1$; the remainder is in $\mathcal{P}_1(m-1)$ with equal weight:
    contribution $B_{m-1}$.
  Hence $B_m = A_m + B_{m-1} = 2B_{m-1} + B_{m-1} = 3 B_{m-1}$.

With $B_0 = 1$: $B_m = 3^m$, and $A_m = 2 B_{m-1} = 2\cdot 3^{m-1}$ for $m \ge 1$.
$\square$

---

## 7. Theorem: the summation

**Theorem.** For all $n \ge 1$,
$$ c_n \;=\; \sum_{s} N(s) \;=\; 3^n - 3\cdot 2^{n-1} + 1. $$

*Proof.* By the Classification in Section 5, the Dyck words of semilength $n$ with
$N(s) \neq 0$ are exactly:

- form (i), parametrized **bijectively** by pairs $(a, T)$ with $1 \le a \le n$ and
  $T \in \mathcal{P}_0(n-a)$, via $s = U^a D^a T$. (The parameters are recovered from
  $s$: $a$ is the first ascent — note the $(a{+}1)$-st step of $U^aD^aT$ is $D$ — and
  $T$ is the part after $q_a = 2a$. Every such $s$ is a Dyck word of form (i): heights
  are nonnegative throughout, there are no gap openers, and $T$'s $U$'s start at
  height $\le 1$.)
- form (ii), parametrized bijectively by triples $(a, i, T)$ with $2 \le a \le n-1$,
  $1 \le i \le a-1$, $T \in \mathcal{P}_1(n-a-1)$, via $s = U^a D^i U D^{a-i} T$.
  (Recovery: $a$ = first ascent, the gap opener and $i$ are visible, $T$ = part after
  $q_a$, which starts at height $1$. The constraint $a \le n-1$ is the existence of arc
  $B = a+1$; $U$-count: $a + 1 + (n-a-1) = n$.)

The two families are disjoint (presence of a gap opener) and exhaust all shapes with
$N(s) \ne 0$ (Lemma B). Summing Lemma B's values:

$$ c_n = \underbrace{\sum_{a=1}^{n} 2^{a-1} \sum_{T \in \mathcal{P}_0(n-a)} 2^{u_0(T)}}_{S_{\mathrm{I}}}
 \;+\; \underbrace{\sum_{a=2}^{n-1} \sum_{i=1}^{a-1} 2^{i} \sum_{T \in \mathcal{P}_1(n-a-1)} 2^{u_0(T)}}_{S_{\mathrm{II}}}
 = \sum_{a=1}^{n} 2^{a-1} A_{n-a} + \sum_{a=2}^{n-1} (2^a - 2)\, B_{n-a-1}, $$

using $\sum_{i=1}^{a-1} 2^i = 2^a - 2$.

**Computing $S_{\mathrm{I}}$.** Separate the term $a = n$ (where $A_0 = 1$) and use
$A_m = 2\cdot3^{m-1}$ for $m \ge 1$:
$$ S_{\mathrm{I}} = 2^{n-1} + \sum_{a=1}^{n-1} 2^{a-1} \cdot 2 \cdot 3^{n-a-1}
 = 2^{n-1} + \sum_{a=1}^{n-1} 2^{a} \, 3^{\,n-1-a}. $$
By the geometric identity $\;3^k - 2^k = \sum_{c=0}^{k-1} 2^c\, 3^{\,k-1-c}\;$ (proof:
telescoping $\sum_{c=0}^{k-1} (2^c 3^{k-c} - 2^{c+1} 3^{k-1-c}) = 3^k - 2^k\cdot 3^0$,
and each summand is $2^c 3^{k-1-c}(3-2) = 2^c 3^{k-1-c}$), applied with $k = n-1$ after
the index shift $a = c+1$:
$$ \sum_{a=1}^{n-1} 2^{a} 3^{\,n-1-a} = 2 \sum_{c=0}^{n-2} 2^{c} 3^{\,n-2-c}
 = 2\,(3^{n-1} - 2^{n-1}). $$
Hence $S_{\mathrm{I}} = 2^{n-1} + 2\cdot 3^{n-1} - 2^{n} = 2\cdot3^{n-1} - 2^{n-1}$.

**Computing $S_{\mathrm{II}}$.** For $n \le 2$ the sum is empty: $S_{\mathrm{II}} = 0 =
3^{n-1} - 2^n + 1$ for $n \in \{1,2\}$. For $n \ge 3$, with $B_m = 3^m$:
$$ S_{\mathrm{II}} = \sum_{a=2}^{n-1} (2^a - 2)\, 3^{\,n-1-a}
 = \Bigl(\sum_{a=1}^{n-1} 2^{a} 3^{\,n-1-a} - 2\cdot 3^{\,n-2}\Bigr)
 - 2 \sum_{a=2}^{n-1} 3^{\,n-1-a}. $$
The first bracket is $2(3^{n-1} - 2^{n-1}) - 2\cdot 3^{n-2}$; the last sum is
$\sum_{t=0}^{n-3} 3^t = \tfrac{3^{n-2}-1}{2}$. So
$$ S_{\mathrm{II}} = 2\cdot 3^{n-1} - 2^{n} - 2\cdot 3^{n-2} - 3^{n-2} + 1
 = 2\cdot 3^{n-1} - 3^{n-1} - 2^{n} + 1 = 3^{n-1} - 2^{n} + 1, $$
which also matches the $n \le 2$ values, so it holds for all $n \ge 1$.

**Total.**
$$ c_n = S_{\mathrm{I}} + S_{\mathrm{II}}
 = \bigl(2\cdot3^{n-1} - 2^{n-1}\bigr) + \bigl(3^{n-1} - 2^{n} + 1\bigr)
 = 3^{n} - 3\cdot 2^{n-1} + 1. \qquad \blacksquare $$

---

## 8. Remarks

1. **Where the "$3$" and the "$2$"s come from.** $B_m = 3^m$ reflects a three-letter
   alphabet of tail blocks ($D$ to the floor; an $\mathsf{L}$-arc or an $\mathsf{H}$-arc
   hung on the current open arc); the $3^n$ main term is the staircase-with-decorations
   bulk, while the $-3\cdot 2^{n-1} + 1$ corrections come from boundary terms of the two
   geometric sums.
2. **The sign word is a 2-coloring.** Condition 2 of Theorem A says $\varepsilon$
   properly 2-colors the graph $G(s)$ on $\{2..n\}$ joining $K<J$ when $J$ is late and
   crosses $K$. Lemma B is then: $N(s) = 2^{\#\mathrm{components}}$ if $G(s)$ is
   bipartite and $0$ otherwise; forms (i)/(ii) make $G(s)$ an explicit forest (isolated
   vertices $\{2..a\}$ resp. $\{2..i\}$; a star $B$–$\{i+1..a\}$ in form (ii); each
   height-1 tail opener hangs a leaf). We chose the direct queue/scan formulation to
   keep the proof self-contained and Lean-friendly (no graph theory needed).
3. **Identity-labeled avoiders.** $\varepsilon \equiv \mathsf{H}$ (i.e. $p =
   \mathrm{id}$) is valid iff no late opener sees an open arc, i.e. $s = U^aD^a(UD)^{n-a}$:
   exactly $n$ shapes — matching the observation recorded in `DEFINITIONS.md` (Section 5).
4. **Lean formalization notes.** All objects are finite and all maps explicit. The
   proof uses only: finite words, the two pattern-criteria (Lemma 1), one induction
   over positions (the scan in Lemma B), and two linear recurrences (Lemma C). No
   generating functions, no graph theory, no sign-reversing involutions.

---

## 9. Numeric validation log

All scripts in `../work/` (Python 3.11); ground-truth data in `../data/`
(`refined_stats.json` produced by the independent Rust enumerator `enumerator.rs`,
bitwise-identical to `enumerator.py` for $n \le 7$).

| Claim | Test | Range | Result |
|---|---|---|---|
| Lemma 0 | set equality: literal $1221/2112$ filter = sorted-closer criterion = $\mathrm{wd}(s,p)$ image | $n \le 5$ (all $\binom{2n}{2,\dots,2}$ words) | `verify_draft.py` L0 OK |
| Lemma 1 | $\star$-criteria vs literal 4-index containment definition | $n \le 4$ all words; $n=5$ all nonnesting | `verify_draft.py` L1 OK |
| Lemma 2 | every avoider is prefix-interval | $n \le 7$ exhaustive | `verify_draft.py` L2 OK |
| Theorem A | predicate 1+2 $\equiv$ brute-force avoidance, pair by pair | all $n!\,\mathrm{Cat}_n$ pairs, $n \le 7$ (2,262,611 pairs total, of which 2,162,160 at $n{=}7$); zero mismatches | `verify_draft.py`, also `verify_theoremA.py` |
| Theorem A at $n=8$ | per-shape predicted counts vs independent Rust enumeration; plus explicit generation of all predicted $\varepsilon$, each checked to be a true avoider (set equality given count equality) | all 1430 shapes, $n=8$ | `verify_theoremA.py`, `verify_final.py` check (2) |
| Lemma B | form classification + $2^{(a-1)+u_0}$ / $2^{i+u_0}$ / $0$ vs brute force per shape | every shape, $n \le 7$; every shape vs Rust data $n \le 8$ | `verify_draft.py` LB OK |
| (graph form of B) | bipartite-forest formula $2^{\#\mathrm{comp}}$, canonical form, $\#$edges count | every shape, $n \le 14$ | `verify_shapes.py` (S2, S3: 0 mismatches) |
| Lemma C | $A_m, B_m$ closed forms vs direct weighted path enumeration | $m \le 9$ (and DP cross-check $m \le 39$) | `verify_draft.py` LC OK; `verify_final.py` check (3) |
| Theorem (sum) | closed-form $S_{\mathrm I}+S_{\mathrm{II}}$ vs $3^n - 3\cdot2^{n-1}+1$ | $n \le 300$ exact integers | `verify_draft.py` SUM OK |
| Theorem (sum) | shape-by-shape $\sum_s N(s)$ via Lemma B formula | $n \le 12$; via graph form $n \le 14$ | `verify_draft.py`, `verify_shapes.py` |
| Conjecture itself | brute force, three independent implementations (Python, Rust, Codex clean-room) | $n \le 8$: counts 1, 4, 16, 58, 196, 634, 1996, 6178 | `../data/validation.json` |

## 10. Honest gap list

None known. Specifically:

- Every lemma above is stated with explicit hypotheses and proved completely; each
  bijection has an explicit inverse with a uniqueness argument (Fact 2.1, Lemma B's
  restriction maps, the two parametrizations in Section 7).
- Edge cases checked in-proof: $n = 1$ ($c_1 = S_{\mathrm I} = A_0 = 1$); $a = n$
  ($T$ empty); $a = 1$ (no gap interval); $i = a-1$ (singleton $\mathrm{open}(o_B)$);
  $S_{\mathrm{II}}$ empty for $n \le 2$.
- The only externally quoted ingredients are the problem's own conventions
  (`DEFINITIONS.md`, pinned verbatim to the published paper).
- Independent hostile review by Codex (GPT-5.5, xhigh reasoning, thread
  `019eb9cd-8cd4-7aa2-8a2d-c9abb70766ae`, June 2026). Verdict: **"CORRECT WITH MINOR
  FIXES … I found no mathematical gap and no counterexample in the lemma chain."**
  Its three findings (all wording/expansion level) are incorporated in this version:
  (1) Observation 5.0(i) now handles $a=n$ explicitly (no late arcs, $q_{a+1}$
  undefined); (2) the ($\mathrm{A}_i$) case of Theorem A is now written out in full
  rather than "by symmetry"; (3) Lemma C's $B$-recurrence now notes the next step
  exists before arguing it must be $D$. Codex additionally ran its own clean-room
  verifications (not reusing this project's scripts): a fresh Theorem A checker over
  all $n!\,\mathrm{Cat}_n$ pairs for $n \le 6$ (zero mismatches) and an independent
  sign-word enumeration of Lemma B / the classification through $n = 9$, totals
  $1, 4, 16, 58, 196, 634, 1996, 6178, 18916$ (zero mismatches). A second, targeted
  hostile pass (same thread) stress-tested (a) the Lemma B scan bijections (including
  $Z(J) = B$ and $i = a-1$), (b) the exhaustiveness/bijectivity of the Section 7
  parametrizations (including empty $T$, $a = n$, $n-a-1 = 0$), and (c) the Lemma 2
  minimal-counterexample occurrence under the biconditional convention, each backed by
  fresh independent enumerations (to $n = 10$, $n = 11$, and $n = 7$ respectively),
  with no failures. **Final Codex verdict on this version: "CORRECT."**
