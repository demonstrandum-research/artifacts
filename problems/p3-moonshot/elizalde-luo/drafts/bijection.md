# A direct bijection proving the Elizalde–Luo conjecture for $\{1132, 3312\}$

**Status: complete proof draft (no known gaps). Every lemma verified numerically for
$n \le 10$; see the validation log in Section 11.**

**Conjecture (Elizalde–Luo, arXiv:2412.00336, DMTCS 27:1 (2025), Table 4).** The number
of nonnesting permutations of the multiset $[n]_2 = \{1,1,2,2,\dots,n,n\}$ avoiding the
patterns $1132$ and $3312$ equals
$$ c_n \;=\; 3^n - 3\cdot 2^{n-1} + 1 \qquad (n \ge 1). $$

**Method.** We construct an explicit bijection
$$ \Phi \;:\; \{\text{avoiders of } [n]_2\} \;\longrightarrow\; W_n, $$
where $W_n \subseteq \{\mathsf{A},\mathsf{B},\mathsf{C}\}^n$ is the explicit language
$$ W_n \;=\; \{\mathsf{A},\mathsf{B},\mathsf{C}\}^n \;\setminus\;
   \Bigl( \underbrace{\mathsf{B}\{\mathsf{A},\mathsf{B}\}^{n-1}}_{2^{n-1}\text{ words}}
   \;\cup\; \underbrace{\mathsf{C}\{\mathsf{A},\mathsf{B}\}^{*}\mathsf{C}^{*}
   \cap \{\mathsf{A},\mathsf{B},\mathsf{C}\}^n}_{2^{n}-1\text{ words}} \Bigr), $$
whose cardinality is $3^n - 2^{n-1} - (2^n - 1) = 3^n - 3\cdot 2^{n-1} + 1$ by a
two-line disjointness count (Lemma 7). Both $\Phi$ and its inverse $\Psi$ are given by
explicit, finitely-checkable constructions (a letter-by-letter encoding and a
letter-by-letter parse), suitable for Lean formalization.

All conventions (containment with biconditional equality, nonnesting via $1221/2112$,
raw-word counting) are exactly those pinned in `../DEFINITIONS.md`, quoted verbatim
from the published paper.

**Relation to the sibling draft `dyck-sign.md`.** Sections 1–4 below (Lemmas 0–2 and
Theorem A) are the same structural foundation as `dyck-sign.md` §§1–4, reproduced for
self-containment; they were independently refereed by Codex there. Sections 5–10 are
the new content of this draft: instead of summing per-shape counts (the route taken by
`dyck-sign.md` §§5–7), we package the shape and the sign data into a single ternary
string and exhibit a bijection onto $W_n$, so that the formula falls out of a trivial
cardinality count of one explicit language. The two drafts share their first half and
have logically independent second halves.

---

## 0. Conventions and notation

A *word* is $w = w_1 w_2 \cdots w_{2n}$ over $\{1,\dots,n\}$ using each letter exactly
twice (a permutation of $[n]_2$). Positions are $1$-based.

**Containment.** $w$ contains a pattern $\sigma = \sigma_1\cdots\sigma_k$ if there are
positions $i_1 < \cdots < i_k$ with, for all $r,s$:
$w_{i_r} < w_{i_s} \iff \sigma_r < \sigma_s$ and
$w_{i_r} = w_{i_s} \iff \sigma_r = \sigma_s$. Otherwise $w$ avoids $\sigma$.

**Nonnesting.** $w$ is *nonnesting* if it avoids $1221$ and $2112$.

For each value $v$ let $\mathrm{fst}(v) < \mathrm{snd}(v)$ be the positions of its two
occurrences; the *arc* of $v$ is $(\mathrm{fst}(v), \mathrm{snd}(v))$. A position is an
*opener* if it is the first occurrence of its value, a *closer* otherwise. Two arcs
*nest* if $\mathrm{fst}(u) < \mathrm{fst}(v) < \mathrm{snd}(v) < \mathrm{snd}(u)$.

An *avoider* is a nonnesting word avoiding both $1132$ and $3312$; $c_n$ denotes the
number of avoiders of $[n]_2$.

**Interval convention.** Throughout, $\{u..v\}$ (or $u, \dots, v$) denotes
$\{j \in \mathbb{Z} : u \le j \le v\}$, which is the **empty set** whenever $u > v$;
e.g. $\{2..i\} = \varnothing$ when $i = 1$, and $\{a+1..a\} = \varnothing$.

---

## 1. Lemma 0: nonnesting words = (Dyck shape) $\times$ (label permutation)

Let $s \in \{U,D\}^{2n}$ be a *Dyck word*: $n$ letters $U$, $n$ letters $D$, every
prefix containing at least as many $U$'s as $D$'s. Let $o_1 < \cdots < o_n$ be the
positions of the $U$'s and $q_1 < \cdots < q_n$ those of the $D$'s.

**Fact 0.1.** In a Dyck word, $o_i < q_i$ for all $i$.
*Proof.* The prefix ending at $q_i$ contains $i$ letters $D$, hence at least $i$
letters $U$; the $i$-th $U$ therefore occurs at a position $< q_i$. $\square$

For a Dyck word $s$ and a permutation $p = (p_1,\dots,p_n)$ of $[n]$ define
$\mathrm{wd}(s,p)$ to be the word with $p_i$ at position $o_i$ and at position $q_i$.

**Lemma 0.** A word $w$ is nonnesting if and only if $w = \mathrm{wd}(s,p)$ for a
(unique) Dyck word $s$ and permutation $p$. Here $s$ is the opener/closer indicator of
$w$ and $p_i$ is the value at the $i$-th opener.

*Proof.* **Step 1: $w$ contains $1221$ or $2112$ $\iff$ two arcs of $w$ nest.** An
occurrence $i_1<i_2<i_3<i_4$ of $1221$ has $w_{i_1}=w_{i_4}=:u$ and
$w_{i_2}=w_{i_3}=:v$ with $u<v$ (equal pattern letters force equal values, and each
value occurs exactly twice, so $\{i_1,i_4\}$ are the two occurrences of $u$ and
$\{i_2,i_3\}$ those of $v$). Thus $w$ contains $1221$ iff there are values $u<v$ with
$\mathrm{fst}(u)<\mathrm{fst}(v)<\mathrm{snd}(v)<\mathrm{snd}(u)$. Symmetrically, $w$
contains $2112$ iff the same holds for some $u>v$. Avoiding both $=$ no two arcs nest.

**Step 2: no two arcs nest $\iff$ openers and closers are matched in the same order.**
($\Leftarrow$) If $\mathrm{fst}(u)<\mathrm{fst}(v)$ always implies
$\mathrm{snd}(u)<\mathrm{snd}(v)$, nesting is impossible. ($\Rightarrow$) If
$\mathrm{fst}(u)<\mathrm{fst}(v)$ and $\mathrm{snd}(v)<\mathrm{snd}(u)$, then since
$\mathrm{fst}(v)<\mathrm{snd}(v)$ the arcs nest. So nonnesting $\iff$ the order of
values by first occurrence equals the order by second occurrence, i.e. the $i$-th
closer carries the value of the $i$-th opener ("FIFO matching").

**Step 3: the bijection.** Given nonnesting $w$, its opener/closer indicator $s$ is a
Dyck word (each closer's opener precedes it), and with $p_i :=$ value at the $i$-th
opener, Step 2 gives $w = \mathrm{wd}(s,p)$. Conversely, in $\mathrm{wd}(s,p)$ the
$i$-th $U$-position is the first occurrence of $p_i$ (any earlier position carries
$p_j$ with $j<i$: an earlier $U$ is the $j$-th with $j<i$; an earlier $D$ is the $j$-th
$D$, which is preceded by at least $j$ $U$'s, so $j \le i-1$), so by Fact 0.1 the arc of
$p_i$ is $(o_i, q_i)$; arcs simultaneously sorted by opener and closer never nest,
hence $\mathrm{wd}(s,p)$ is nonnesting. The two constructions are mutually inverse.
$\square$

From now on a nonnesting word is identified with its pair $(s,p)$: *arc $i$* has opener
$o_i$, closer $q_i$, value $p_i$. We say arc $K$ is **open at position $t$** if
$o_K < t < q_K$, and write $\mathrm{open}(t) = \{K : o_K < t < q_K\}$. (We only use
this with $t = o_J$, $J \neq K$, so ties cannot occur.)

---

## 2. Lemma 1: a positional criterion for containing 1132 / 3312

**Lemma 1.** Let $w$ be a permutation of $[n]_2$.
1. $w$ contains $1132 \iff$ there exist a value $v$ and positions $t < t'$, both
   $> \mathrm{snd}(v)$, with $w_t > w_{t'} > v$.
2. $w$ contains $3312 \iff$ there exist a value $v$ and positions $t < t'$, both
   $> \mathrm{snd}(v)$, with $w_t < w_{t'} < v$.

*Proof.* (1, $\Leftarrow$) The subsequence at positions
$\mathrm{fst}(v) < \mathrm{snd}(v) < t < t'$ is $(v, v, w_t, w_{t'})$. Compare with
$1132$: the equalities ($\sigma_1=\sigma_2$ only) and the strict relations
($v < w_{t'} < w_t$, hence also $w_t \ne w_{t'}$, $w_t \ne v$, $w_{t'} \ne v$) match
exactly, so this is an occurrence. (1, $\Rightarrow$) In an occurrence
$i_1<i_2<i_3<i_4$ of $1132$, $w_{i_1}=w_{i_2}=:v$ forces $i_2 = \mathrm{snd}(v)$, and
the pattern forces $w_{i_3} > w_{i_4} > v$; take $t=i_3$, $t'=i_4$. (2) Same with all
inequalities reversed. $\square$

**Corollary 1.1.** A nonnesting word $(s,p)$ is an avoider iff for every $i \in [n]$
there is no pair $t<t'$, both $>q_i$, with
- ($\mathrm{D}_i$): $w_t > w_{t'} > p_i$, nor
- ($\mathrm{A}_i$): $w_t < w_{t'} < p_i$.

*Proof.* Lemma 1 with $\mathrm{snd}(p_i) = q_i$ (Lemma 0). $\square$

---

## 3. The sign word: avoiders have prefix-interval labels

Call $p \in S_n$ **prefix-interval** if every prefix set $\{p_1,\dots,p_j\}$ is an
interval of integers; equivalently, for each $j \ge 2$ either
$p_j = \min\{p_1..p_{j-1}\}-1$ (write $\varepsilon_j = \mathsf{L}$) or
$p_j = \max\{p_1..p_{j-1}\}+1$ (write $\varepsilon_j = \mathsf{H}$). The word
$\varepsilon = (\varepsilon_2, \dots, \varepsilon_n) \in \{\mathsf{L},\mathsf{H}\}^{n-1}$
is the **sign word** of $p$. For $x \in \{\mathsf{L},\mathsf{H}\}$, $\bar{x}$ denotes
the other letter.

**Fact 3.1 (bijection).** $p \mapsto \varepsilon$ is a bijection from prefix-interval
permutations of $[n]$ onto $\{\mathsf{L},\mathsf{H}\}^{n-1}$.
*Proof.* Given $\varepsilon$, the $\mathsf{L}$-steps fill values below $p_1$ and the
$\mathsf{H}$-steps above, so necessarily
$p_1 = 1 + \#\{j : \varepsilon_j = \mathsf{L}\}$, and then every $p_j$ is determined
(current min $-1$ or current max $+1$); this always yields a permutation of $[n]$, and
the two maps are mutually inverse. $\square$

**Fact 3.2 (comparison rule).** If $p$ is prefix-interval with sign word $\varepsilon$,
then for all $1 \le u < v \le n$: $p_u < p_v \iff \varepsilon_v = \mathsf{H}$ and
$p_u > p_v \iff \varepsilon_v = \mathsf{L}$.
*Proof.* $\varepsilon_v = \mathsf{H}$ gives $p_v = \max\{p_1..p_{v-1}\}+1 > p_u$;
$\varepsilon_v = \mathsf{L}$ gives $p_v < p_u$. Exhaustive and exclusive. $\square$

**Lemma 2.** If $(s,p)$ is an avoider then $p$ is prefix-interval.

*Proof.* Suppose not; let $j$ be minimal with $\{p_1..p_j\}$ not an interval. Then
$j \ge 2$, $I := \{p_1..p_{j-1}\}$ is an interval $[lo,hi]$, and $p_j \notin [lo-1,
hi+1]$.

*Case $p_j \ge hi+2$.* Let $h := p_j - 1$; then $hi < h < p_j$, so $h \notin I \cup
\{p_j\}$, hence $h = p_m$ for some $m > j$. The positions $q_1 < q_j < q_m$ carry
$w_{q_j} = p_j > w_{q_m} = h > hi \ge p_1$, so ($\mathrm{D}_1$) of Corollary 1.1 is
violated: $w$ contains $1132$, contradiction.

*Case $p_j \le lo-2$.* Let $h := p_j + 1 < lo$; again $h = p_m$, $m > j$. Then
$q_1 < q_j < q_m$ with $w_{q_j} = p_j < w_{q_m} = h < lo \le p_1$ violates
($\mathrm{A}_1$): $w$ contains $3312$, contradiction. $\square$

*(Prefix-interval permutations are the classical $\{132,312\}$-avoiders; we do not need
this fact.)*

---

## 4. Theorem A: the structural characterization

Fix a Dyck word $s$; let $a = a(s) \ge 1$ be its first ascent (number of $U$'s before
the first $D$), so the openers $o_1, \dots, o_a$ are at positions $1, \dots, a$ and
$q_1 = a+1$. Call arc $J$ **late** if $o_J > q_1$, i.e. (see Lemma 3 below for the
equivalent index form) iff $J \ge a+1$.

**Observation 4.1.** If $J$ is late, every $K \in \mathrm{open}(o_J)$ satisfies
$2 \le K < J$. *Proof.* $o_K < o_J$ gives $K < J$; $K = 1$ would need $q_1 > o_J$,
contradicting lateness. $\square$

**Theorem A.** A pair $(s,p)$ is an avoider if and only if
1. $p$ is prefix-interval, with sign word $\varepsilon$; and
2. for every late arc $J$ and every $K \in \mathrm{open}(o_J)$:
   $\varepsilon_K \neq \varepsilon_J$.

*Proof.* **($\Rightarrow$).** Condition 1 is Lemma 2. For condition 2, let $J$ be late,
$K \in \mathrm{open}(o_J)$ (so $2 \le K < J$ by Observation 4.1). Suppose
$\varepsilon_K = \varepsilon_J = \mathsf{H}$. By Fact 3.2, $p_J > p_K$ and
$p_K > p_1$. Take $t = o_J < t' = q_K$ (openness gives $o_J < q_K$); both exceed
$q_1$ (lateness; and $q_K > o_J > q_1$); and $w_t = p_J > w_{t'} = p_K > p_1$,
violating ($\mathrm{D}_1$) — contradiction. If
$\varepsilon_K = \varepsilon_J = \mathsf{L}$, Fact 3.2 gives $p_J < p_K < p_1$ and the
same positions violate ($\mathrm{A}_1$) — contradiction.

**($\Leftarrow$).** Suppose 1 and 2 hold but some ($\mathrm{D}_i$) or ($\mathrm{A}_i$)
is violated.

*Case ($\mathrm{D}_i$):* positions $t<t'$, both $>q_i$, with $w_t > w_{t'} > p_i$. Let
$A, B$ be the arcs of $t, t'$; $A \ne B$ since $w_t \ne w_{t'}$. Every arc $C \le i$
has both positions $\le q_i$ ($o_C < q_C \le q_i$), so $A, B > i$. Now:
- $p_B > p_i$, $i < B$ forces $\varepsilon_B = \mathsf{H}$ (Fact 3.2).
- If $A < B$ then $\varepsilon_B = \mathsf{H}$ gives $p_A < p_B$, contradicting
  $w_t > w_{t'}$. So $B < A$.
- $p_A > p_B$, $B < A$ forces $\varepsilon_A = \mathsf{H}$.
- $t \in \{o_A, q_A\}$, $t' \in \{o_B, q_B\}$, $t < t'$. From $B < A$: $o_B < o_A$,
  $q_B < q_A$. If $t = q_A$ then $t' > q_A$, but both positions of $B$ are $< q_A$ —
  impossible. So $t = o_A$; $t' = o_B$ is impossible ($o_B < o_A$), so $t' = q_B$,
  giving $o_B < o_A < q_B$, i.e. $B \in \mathrm{open}(o_A)$.
- $A$ is late: $o_A = t > q_i \ge q_1$.

So $A$ late, $B \in \mathrm{open}(o_A)$,
$\varepsilon_B = \varepsilon_A = \mathsf{H}$ — contradicting 2.

*Case ($\mathrm{A}_i$):* positions $t<t'$, both $>q_i$, with $w_t < w_{t'} < p_i$.
As before $A \ne B$, $A, B > i$. Then: $p_B < p_i$, $i<B$ forces
$\varepsilon_B = \mathsf{L}$; if $A < B$, $\varepsilon_B = \mathsf{L}$ gives
$p_A > p_B$, contradicting $w_t < w_{t'}$, so $B < A$; $p_A < p_B$, $B<A$ forces
$\varepsilon_A = \mathsf{L}$; the position analysis is identical to the previous case
($t = o_A$, $t' = q_B$, $B \in \mathrm{open}(o_A)$, $A$ late). So
$\varepsilon_B = \varepsilon_A = \mathsf{L}$ with $A$ late,
$B \in \mathrm{open}(o_A)$ — contradicting 2. $\square$

**Definition.** $\varepsilon \in \{\mathsf{L},\mathsf{H}\}^{n-1}$ (indexed
$2,\dots,n$) is **valid for $s$** if condition 2 of Theorem A holds. By Lemma 0,
Theorem A and Fact 3.1,
$$ \{\text{avoiders}\} \;\longleftrightarrow\;
   \{(s,\varepsilon) : s \text{ Dyck word of semilength } n,\;
     \varepsilon \text{ valid for } s\} $$
is a bijection (explicit in both directions: $w \mapsto (s, \varepsilon(p))$ and
$(s,\varepsilon) \mapsto \mathrm{wd}(s, p(\varepsilon))$).

---

## 5. The shape classification

**Lemma 3 (FIFO interval).** Let $s$ be a Dyck word, $J \in [n]$, and let $c$ be the
number of closers (positions of $D$'s) before $o_J$. Then
$$ \mathrm{open}(o_J) = \{c+1, c+2, \dots, J-1\}, $$
and the height of $s$ before its $J$-th $U$-step is $J - 1 - c = |\mathrm{open}(o_J)|$.

*Proof.* The arcs opened before $o_J$ are exactly $1, \dots, J-1$. The closers before
$o_J$ are an initial segment of $q_1 < q_2 < \cdots$, hence are exactly
$q_1, \dots, q_c$, i.e. arcs $1, \dots, c$ are closed before $o_J$ and arcs
$c+1, \dots, J-1$ are open. ($c \le J-1$ since each closed arc was opened.) The height
before a position equals #openers $-$ #closers among earlier positions. $\square$

In particular, *arc $J$ is late iff $J \ge a+1$*: openers $1..a$ are at positions
$1..a < q_1 = a+1$, and openers $a+1, \dots, n$ are at positions $> q_1$ (position
$a+1$ is a $D$).

Fix $s$ with first ascent $a$. Define:
- a **gap opener**: an opener position strictly between $q_1$ and $q_a$ (for $a = 1$
  this interval is empty);
- a **tail opener**: an opener position $> q_a$; the corresponding arcs are **tail
  arcs**. For a tail arc $j$ let $\delta_j \in \{0, 1, 2, \dots\}$ be the height of $s$
  before that $U$-step (its *start height*).

**Lemma 4 (obstructions).** If $s$ has at least two gap openers, or a tail opener with
start height $\ge 2$, then no $\varepsilon$ is valid for $s$.

*Proof.* *Two gap openers.* Then $a \ge 2$. The openers in the interval $(q_1, q_a)$
belong to arcs $a+1, a+2, \dots$ in order; let $\beta = a+1 < \beta' = a+2$ be the arcs
of the first two. Both are late. Let $c$ (resp. $c'$) be the number of closers before
$o_\beta$ (resp. $o_{\beta'}$). Since $q_1 < o_\beta \le o_{\beta'} - 1$ and
$o_{\beta'} < q_a$: $1 \le c \le c' \le a - 1$. By Lemma 3,
$\mathrm{open}(o_\beta) = \{c+1,\dots,a\} \ni a$ and
$\mathrm{open}(o_{\beta'}) = \{c'+1,\dots,a+1\} \supseteq \{a, \beta\}$. If
$\varepsilon$ were valid: validity at $\beta$ gives
$\varepsilon_\beta \neq \varepsilon_a$, so
$\{\varepsilon_a, \varepsilon_\beta\} = \{\mathsf{L},\mathsf{H}\}$; validity at
$\beta'$ needs $\varepsilon_{\beta'} \notin \{\varepsilon_a, \varepsilon_\beta\}$ —
impossible.

*Tail opener at height $\ge 2$.* Let $J$ be its arc: $o_J > q_a$ and, by Lemma 3,
$\mathrm{open}(o_J) = \{c+1, \dots, J-1\}$ with $J-1-c \ge 2$; so
$K := J-2$ and $K' := J-1$ both lie in $\mathrm{open}(o_J)$. $K'$ is late: $q_{K'} >
o_J > q_a$ forces $K' > a$, i.e. $K' \ge a+1$. Also $K \in \mathrm{open}(o_{K'})$:
$o_K < o_{K'}$ and $q_K > o_J > o_{K'}$. If $\varepsilon$ were valid: validity at $K'$
gives $\varepsilon_{K'} \ne \varepsilon_K$, and validity at $J$ needs
$\varepsilon_J \notin \{\varepsilon_K, \varepsilon_{K'}\} =
\{\mathsf{L},\mathsf{H}\}$ — impossible. $\square$

**Lemma 5 (admissible shapes).** Suppose $s$ has at most one gap opener and all tail
openers start at height $\le 1$. Then exactly one of the following holds, and in each
case $s$ is uniquely determined by the stated parameters; conversely every parameter
choice yields such a Dyck word.

- **(S) Staircase:** $a = n$ and $s = U^n D^n$. (No parameters.)
- **(I)** $1 \le a \le n-1$, no gap opener. The tail arcs are $a+1, \dots, n$;
  $\delta_{a+1} = 0$; $\delta_j \in \{0,1\}$ for $a+2 \le j \le n$; and
  $$ s \;=\; U^a D^a \cdot \mathrm{Tail}\bigl(0;\ \delta_{a+1}, \dots,
     \delta_n\bigr), $$
  where the parameters are $\bigl(a,\ \delta = (\delta_{a+2}, \dots, \delta_n) \in
  \{0,1\}^{n-a-1}\bigr)$ and $\delta_{a+1} := 0$.
- **(II)** $2 \le a \le n-1$, exactly one gap opener, belonging to arc $B := a+1$,
  with $i$ closers before it, $1 \le i \le a-1$; moreover
  $\mathrm{open}(o_B) = \{i+1, \dots, a\}$. The tail arcs are $a+2, \dots, n$ with
  $\delta_j \in \{0,1\}$ unrestricted, and
  $$ s \;=\; U^a D^{\,i}\, U\, D^{\,a-i} \cdot \mathrm{Tail}\bigl(1;\
     \delta_{a+2}, \dots, \delta_n\bigr), $$
  with parameters $\bigl(a, i,\ \delta = (\delta_{a+2}, \dots, \delta_n) \in
  \{0,1\}^{n-a-1}\bigr)$.

Here $\mathrm{Tail}(h_0;\ d_1, \dots, d_m)$, for $m \ge 0$ and $d_r \in \{0,1\}$ with
$d_1 \le h_0$ whenever $m \ge 1$, is the $\{U,D\}$-word produced by the following
scan: start with $h := h_0$; for $r = 1, \dots, m$ emit $D^{\,h - d_r}$ then $U$ and
set $h := d_r + 1$; finally emit $D^{\,h}$. (All $D$-run lengths are $\ge 0$:
$d_1 \le h_0$, and for $r \ge 2$, $d_r \le 1 \le d_{r-1} + 1 = h$. For $m = 0$ the
word is just $D^{\,h_0}$.)

*Proof.* If $a = n$, $s = U^n D^n$: case (S). Let $a < n$.

*No gap opener.* Every position in $(q_1, q_a)$ is a closer; since
$q_1 < q_2 < \cdots < q_a$ are the only closers $\le q_a$ and no openers interleave
($q_1 = a+1$), $q_m = a+m$ for $m \le a$: the word begins $U^a D^a$. All arcs
$\ge a+1$ open after $q_a = 2a$: the tail arcs are exactly $a+1, \dots, n$ (nonempty
since $a<n$). The height after position $2a$ is $0$ and the next position is an opener
(a $D$ would make the height negative), so $\delta_{a+1} = 0$; by hypothesis
$\delta_j \le 1$ for the others. The rest of the word is forced by the start heights:
between consecutive tail openers all positions are closers, and the height must drop
from $\delta_j + 1$ (just after the $U$ of arc $j$) to $\delta_{j+1}$ (just before the
$U$ of arc $j+1$): exactly $\delta_j + 1 - \delta_{j+1}$ letters $D$; after the last
opener the height $\delta_n + 1$ must return to $0$. This is precisely
$\mathrm{Tail}(0; \delta_{a+1}, \dots, \delta_n)$, proving the factorization and that
$(a,\delta) \mapsto s$ is injective on this case. Conversely, for any such
$(a, \delta)$ the displayed word is a Dyck word of semilength $n$ in case (I): the
scan keeps $h \ge 0$ everywhere and ends at $0$ (so #$D$ = #$U$), the number of $U$'s
is $a + (n-a) = n$, the first ascent is $a$ (the scan's first emission for $r=1$ is
$D^0 U$... preceded by $D^a$, so position $a+1$ is a $D$), there is no gap opener
(positions $a+1..2a$ are $D$'s and $q_a = 2a$), and the tail start heights are
$\delta_{a+1}, \dots, \delta_n$ by construction.

*One gap opener.* It is the first opener after $q_1$, i.e. $o_{a+1}$, so $B = a+1$;
$a \ge 2$ (the interval $(q_1,q_a)$ must be nonempty to contain it). With $i :=$
#closers before $o_B$: $1 \le i$ ($o_B > q_1$) and $i \le a - 1$ ($o_B < q_a$).
Positions in $(q_1, q_a)$ other than $o_B$ are closers, so the prefix up to $q_a$
reads $U^a D^i U D^{a-i}$ (closers $q_1..q_i$, then $o_B$, then $q_{i+1}..q_a$); by
Lemma 3, $\mathrm{open}(o_B) = \{i+1, \dots, a\}$. After $q_a$ (position $2a+1$) the
height is $(a+1) - a = 1$. The tail arcs are $a+2, \dots, n$ (possibly none), and the
same forced-$D$-run argument identifies the remainder of the word with
$\mathrm{Tail}(1; \delta_{a+2}, \dots, \delta_n)$ — for $a = n-1$ this is
$\mathrm{Tail}(1;\,) = D$, i.e. $s = U^aD^iUD^{a-i}D$. Hence $(a,i,\delta) \mapsto s$
is injective on this case; conversely each $(a,i,\delta)$ yields a Dyck word of case
(II) by the same checks ($U$-count $a + 1 + (n-a-1) = n$; first ascent $a$; exactly
one gap opener, with $i$ closers before it; tail start heights $\delta_j$). $\square$

Cases (S), (I), (II) are pairwise disjoint (by $a = n$ vs. $a<n$, and by the absence
vs. presence of a gap opener) and by Lemma 4 they exhaust all shapes admitting a valid
$\varepsilon$.

---

## 6. Valid sign words on admissible shapes

**Lemma 6 (local form of validity).** Let $s$ be admissible and
$\varepsilon \in \{\mathsf{L},\mathsf{H}\}^{n-1}$ (indexed $2..n$).

- **(S):** every $\varepsilon$ is valid. (There are no late arcs.)
- **(I):** $\varepsilon$ is valid $\iff$ for every tail arc $j \ge a+2$ with
  $\delta_j = 1$: $\varepsilon_j = \overline{\varepsilon_{j-1}}$.
  In particular $\varepsilon_2, \dots, \varepsilon_{a+1}$ and $\varepsilon_j$ for
  tail arcs with $\delta_j = 0$ are unconstrained.
- **(II):** $\varepsilon$ is valid $\iff$
  $\varepsilon_{i+1} = \cdots = \varepsilon_a = \overline{\varepsilon_{a+1}}$ and for
  every tail arc $j \ge a+2$ with $\delta_j = 1$:
  $\varepsilon_j = \overline{\varepsilon_{j-1}}$.
  In particular $\varepsilon_2, \dots, \varepsilon_i$, $\varepsilon_{a+1}$, and
  $\varepsilon_j$ for tail arcs with $\delta_j = 0$ are unconstrained.

*Proof.* Validity is the conjunction, over late arcs $J$ (i.e. $J \ge a+1$, Lemma 3)
of: $\varepsilon_J \ne \varepsilon_K$ for all $K \in \mathrm{open}(o_J)$. We compute
$\mathrm{open}(o_J)$ for each late arc using Lemma 3.

(S): no late arcs; the conjunction is empty.

(I): For $J = a+1$: the closers before $o_{a+1} = 2a+1$ are $q_1, \dots, q_a$, so
$\mathrm{open}(o_{a+1}) = \{a+1, \dots, a\} = \varnothing$ — no constraint. For a tail
arc $J \ge a+2$: $|\mathrm{open}(o_J)| = \delta_J \in \{0,1\}$. If $\delta_J = 0$: no
constraint. If $\delta_J = 1$: $\mathrm{open}(o_J) = \{c+1..J-1\}$ of size one, i.e.
$= \{J-1\}$, and the constraint $\varepsilon_J \ne \varepsilon_{J-1}$ is (for a
two-letter alphabet) $\varepsilon_J = \overline{\varepsilon_{J-1}}$. The conjunction
of exactly these constraints is the stated condition.

(II): For $J = B = a+1$: $\mathrm{open}(o_B) = \{i+1, \dots, a\}$ (Lemma 5), so the
constraint is $\varepsilon_{a+1} \ne \varepsilon_K$ for all $K \in \{i+1..a\}$, which
(two letters) holds iff $\varepsilon_{i+1} = \cdots = \varepsilon_a =
\overline{\varepsilon_{a+1}}$. For tail arcs $J \ge a+2$: exactly as in (I)
($\delta_J = 1 \Rightarrow \mathrm{open}(o_J) = \{J-1\}$; note for $J = a+2$ this is
$\{a+1\} = \{B\}$). $\square$

**Corollary 6.1 (free-coordinate parametrization).** For each admissible $s$, let
$F(s) \subseteq \{2,\dots,n\}$ be the *free set*:
$$ F(s) = \begin{cases}
\{2..n\} & (S)\\
\{2..a+1\} \cup \{j \ge a+2 : \delta_j = 0\} & (I)\\
\{2..i\} \cup \{a+1\} \cup \{j \ge a+2 : \delta_j = 0\} & (II).
\end{cases} $$
The restriction $\varepsilon \mapsto \varepsilon|_{F(s)}$ is a bijection from valid
sign words onto $\{\mathsf{L},\mathsf{H}\}^{F(s)}$.

*Proof.* Define the extension map $E$ of $f \in \{\mathsf{L},\mathsf{H}\}^{F(s)}$: set
$\varepsilon_j := f_j$ on $F(s)$; in case (II) set $\varepsilon_{i+1} = \cdots =
\varepsilon_a := \overline{f_{a+1}}$; then process tail arcs $j = a+2, \dots, n$ in
increasing order, setting $\varepsilon_j := \overline{\varepsilon_{j-1}}$ whenever
$\delta_j = 1$ (the reference $\varepsilon_{j-1}$ is already defined: $j - 1$ is
either in $F(s)$, or in the block $\{i+1..a\}$, or $= a+1$, or an earlier-processed
tail arc). $E(f)$ satisfies the conditions of Lemma 6 by construction, hence is valid,
and clearly $E(f)|_{F(s)} = f$. Conversely, if $\varepsilon$ is valid then by Lemma 6
its non-free coordinates are determined from $\varepsilon|_{F(s)}$ by exactly the
assignments $E$ makes (block coordinates equal $\overline{\varepsilon_{a+1}}$;
$\delta_j = 1$ tail coordinates equal $\overline{\varepsilon_{j-1}}$, by induction on
$j$), so $E(\varepsilon|_{F(s)}) = \varepsilon$. $\square$

---

## 7. The target language $W_n$

Work over the alphabet $\{\mathsf{A}, \mathsf{B}, \mathsf{C}\}$. Identify signs with
letters via
$$ \ell(\mathsf{L}) = \mathsf{A}, \qquad \ell(\mathsf{H}) = \mathsf{B}. $$

**Definition.** $W_n \subseteq \{\mathsf{A},\mathsf{B},\mathsf{C}\}^n$ is the set of
strings $\sigma$ such that:
- if $\sigma$ contains no $\mathsf{C}$, then $\sigma_1 = \mathsf{A}$;
- if $\sigma_1 = \mathsf{C}$, then there are positions $2 \le r < t \le n$ with
  $\sigma_r = \mathsf{C}$ and $\sigma_t \ne \mathsf{C}$;
- (if $\sigma_1 \ne \mathsf{C}$ and $\sigma$ contains a $\mathsf{C}$: no condition.)

**Lemma 7 (complement and count).** The complement of $W_n$ in
$\{\mathsf{A},\mathsf{B},\mathsf{C}\}^n$ is the disjoint union of
$$ X_1 = \mathsf{B}\,\{\mathsf{A},\mathsf{B}\}^{n-1} \quad\text{and}\quad
   X_2 = \{\,\mathsf{C}\, v\, \mathsf{C}^k : v \in \{\mathsf{A},\mathsf{B}\}^m,\;
          m, k \ge 0,\; 1 + m + k = n \,\}, $$
with $|X_1| = 2^{n-1}$ and $|X_2| = \sum_{m=0}^{n-1} 2^m = 2^n - 1$. Hence
$$ |W_n| = 3^n - 2^{n-1} - (2^n - 1) = 3^n - 3 \cdot 2^{n-1} + 1
   \qquad (n \ge 1). $$

*Proof.* A string violates the definition iff (no $\mathsf{C}$ and
$\sigma_1 = \mathsf{B}$) — note a $\mathsf{C}$-free string cannot have $\sigma_1 =
\mathsf{C}$ — or ($\sigma_1 = \mathsf{C}$ and no $r \ge 2, t > r$ with $\sigma_r =
\mathsf{C} \ne \sigma_t$). The first family is $X_1$. For the second: write $\sigma =
\mathsf{C}\rho$. The condition "no $\mathsf{C}$ of $\rho$ is followed (anywhere later
in $\rho$) by a non-$\mathsf{C}$" holds iff every letter after the first $\mathsf{C}$
of $\rho$ (if any) is $\mathsf{C}$, i.e. iff $\rho \in
\{\mathsf{A},\mathsf{B}\}^*\mathsf{C}^*$; that family is $X_2$ (with $k = 0$ covering
$\mathsf{C}$-free $\rho$). $X_1$ and $X_2$ are disjoint (first letter $\mathsf{B}$
vs. $\mathsf{C}$), and within $X_2$ the pair $(m,k)$ is determined by $\sigma$, so
$|X_2| = \sum_{m+k = n-1} 2^m = 2^n - 1$. $\square$

*(Check, $n=1$: $X_1 = \{\mathsf{B}\}$, $X_2 = \{\mathsf{C}\}$, $W_1 =
\{\mathsf{A}\}$, $|W_1| = 1 = 3 - 3 + 1$. No special case is needed at $n = 1$.)*

---

## 8. The bijection

**Definition of $\Phi$.** Let $(s, \varepsilon)$ be an admissible shape with a valid
sign word (equivalently, by §4, the pair corresponding to an avoider under the
bijection at the end of Section 4). Define
$\sigma = \Phi(s,\varepsilon) \in \{\mathsf{A},\mathsf{B},\mathsf{C}\}^n$ by cases on
Lemma 5's classification:

- **(S)** ($s = U^nD^n$):
  $$ \sigma_1 = \mathsf{A}; \qquad \sigma_j = \ell(\varepsilon_j) \ \ (2 \le j \le n). $$
- **(I)** (parameters $a, \delta$):
  $$ \sigma_j = \ell(\varepsilon_{j+1}) \ \ (1 \le j \le a); \qquad
     \sigma_{a+1} = \mathsf{C}; $$
  $$ \sigma_j = \begin{cases} \ell(\varepsilon_j) & \delta_j = 0\\
     \mathsf{C} & \delta_j = 1 \end{cases} \ \ (a+2 \le j \le n). $$
- **(II)** (parameters $a, i, \delta$):
  $$ \sigma_1 = \mathsf{C}; \quad
     \sigma_j = \ell(\varepsilon_j) \ \ (2 \le j \le i); \quad
     \sigma_j = \mathsf{C} \ \ (i+1 \le j \le a); \quad
     \sigma_{a+1} = \ell(\varepsilon_{a+1}); $$
  $$ \sigma_j = \begin{cases} \ell(\varepsilon_j) & \delta_j = 0\\
     \mathsf{C} & \delta_j = 1 \end{cases} \ \ (a+2 \le j \le n). $$

(In words: every free coordinate of $\varepsilon$ is written as its letter; every
*forced* arc — block arcs, $\delta = 1$ tail arcs — is written $\mathsf{C}$; in case
(I) the initial free block is shifted one slot left so that position $a+1$ can carry a
$\mathsf{C}$ marking the end of the staircase; in case (II) position 1 carries a
$\mathsf{C}$ marking the presence of the gap opener; in case (S) position 1 carries
the padding letter $\mathsf{A}$.)

**Theorem B.** $\Phi$ is a bijection from
$\{(s,\varepsilon) : s \text{ admissible}, \varepsilon \text{ valid}\}$ onto $W_n$.

*Proof.* **1. $\Phi$ lands in $W_n$, and the three cases have disjoint images.**
- (S): $\sigma$ is $\mathsf{C}$-free with $\sigma_1 = \mathsf{A}$: in $W_n$.
- (I): $\sigma_1 = \ell(\varepsilon_2) \in \{\mathsf{A},\mathsf{B}\}$ and $\sigma$
  contains a $\mathsf{C}$ (at position $a+1 \le n$): in $W_n$ (third bullet of the
  definition).
- (II): $\sigma_1 = \mathsf{C}$; take $r = i+1$ and $t = a+1$: $2 \le i+1 < a+1 \le n$,
  $\sigma_{i+1} = \mathsf{C}$ (the block is nonempty, $i \le a-1$), $\sigma_{a+1} \in
  \{\mathsf{A},\mathsf{B}\}$: in $W_n$ (second bullet).

Disjointness: (S)-images are $\mathsf{C}$-free; (I)-images contain $\mathsf{C}$ and
have $\sigma_1 \ne \mathsf{C}$; (II)-images have $\sigma_1 = \mathsf{C}$.

**2. The parse $\Psi$.** Given $\sigma \in W_n$, define $\Psi(\sigma)$ as follows.

*Case $\mathsf{C} \notin \sigma$.* Then $\sigma_1 = \mathsf{A}$ ($W_n$, first bullet).
Output case (S) with $\varepsilon_j := \ell^{-1}(\sigma_j)$, $2 \le j \le n$.

*Case $\sigma_1 \ne \mathsf{C}$, $\mathsf{C} \in \sigma$.* Let $a + 1$ be the position
of the first $\mathsf{C}$, so $1 \le a \le n - 1$ and
$\sigma_1, \dots, \sigma_a \in \{\mathsf{A},\mathsf{B}\}$. Set
$\varepsilon_{j+1} := \ell^{-1}(\sigma_j)$ for $1 \le j \le a$; for
$j = a+2, \dots, n$ (in increasing order) set $\delta_j := 1$ and
$\varepsilon_j := \overline{\varepsilon_{j-1}}$ if $\sigma_j = \mathsf{C}$, else
$\delta_j := 0$ and $\varepsilon_j := \ell^{-1}(\sigma_j)$. Output case (I) with
parameters $(a, \delta)$ — a well-defined admissible shape by Lemma 5(I) — and the
sign word $\varepsilon$, which is valid by Lemma 6(I) (its $\delta_j = 1$ coordinates
satisfy the forced equalities by construction).

*Case $\sigma_1 = \mathsf{C}$.* Let $i - 1 \ge 0$ be the length of the maximal
$\{\mathsf{A},\mathsf{B}\}$-run starting at position $2$ (so positions $2..i$ are in
$\{\mathsf{A},\mathsf{B}\}$ and position $i+1$, if $\le n$, is $\mathsf{C}$). The
second bullet of $W_n$'s definition provides $2 \le r < t \le n$ with
$\sigma_r = \mathsf{C}$, $\sigma_t \ne \mathsf{C}$. In particular there is a
$\mathsf{C}$ at a position $\ge 2$, so $i + 1 \le n$ and
$\sigma_{i+1} = \mathsf{C}$ (the first such $\mathsf{C}$ is at $i+1$). Let the
maximal $\mathsf{C}$-run starting at position $i+1$ occupy positions
$i+1, \dots, a$. We claim $a \le n-1$ and $\sigma_{a+1} \in
\{\mathsf{A},\mathsf{B}\}$. Indeed, consider the witness pair $(r,t)$; note
$r \ge i+1$ (positions $2..i$ are not $\mathsf{C}$). If $r \le a$: then
$t > r$ and $\sigma_t \ne \mathsf{C}$ force $t \ge a+1$ (positions $r{+}1..a$ are
$\mathsf{C}$), so $a + 1 \le n$; and $\sigma_{a+1} \ne \mathsf{C}$ by maximality of
the run. If $r > a$: then $a + 1 \le r \le n$, so position $a+1$ exists; $r = a+1$ is
impossible ($\sigma_{a+1} = \mathsf{C}$ would extend the maximal run past $a$), so
$\sigma_{a+1} \ne \mathsf{C}$ by maximality. In both cases $a \le n-1$ and
$\sigma_{a+1} \in \{\mathsf{A},\mathsf{B}\}$, as claimed. Set $\varepsilon_j :=
\ell^{-1}(\sigma_j)$ for $2 \le j \le i$;
$\varepsilon_{a+1} := \ell^{-1}(\sigma_{a+1})$;
$\varepsilon_{i+1} = \cdots = \varepsilon_a := \overline{\varepsilon_{a+1}}$; and
process $j = a+2, \dots, n$ exactly as in the previous case (defining $\delta_j$ and
$\varepsilon_j$). Output case (II) with parameters $(a, i, \delta)$ — well defined:
$1 \le i \le a-1 \le n-2$ — and the sign word $\varepsilon$, valid by Lemma 6(II).

**3. $\Psi \circ \Phi = \mathrm{id}$.** Let $(s, \varepsilon)$ be valid, $\sigma =
\Phi(s,\varepsilon)$.
- (S): $\sigma$ is $\mathsf{C}$-free, so $\Psi$ takes the (S)-branch and recovers each
  $\varepsilon_j$.
- (I): $\sigma_1 \ne \mathsf{C}$ and the first $\mathsf{C}$ of $\sigma$ is at position
  $a+1$ — positions $1..a$ carry sign letters. So $\Psi$ takes the (I)-branch and
  recovers $a$; it recovers $\varepsilon_2, \dots, \varepsilon_{a+1}$ from positions
  $1..a$; for $j \ge a+2$ it recovers $\delta_j$ ($\mathsf{C} \leftrightarrow
  \delta_j = 1$) and $\varepsilon_j$ — directly if $\delta_j = 0$, and as
  $\overline{\varepsilon_{j-1}}$ if $\delta_j = 1$, which equals the original
  $\varepsilon_j$ because the original is valid (Lemma 6(I)) — by induction on $j$,
  using that $\varepsilon_{j-1}$ was correctly recovered. By Lemma 5(I), $(a,\delta)$
  determines $s$.
- (II): $\sigma_1 = \mathsf{C}$, so $\Psi$ takes the (II)-branch. In $\sigma$,
  positions $2..i$ are sign letters, position $i+1$ is $\mathsf{C}$ (block nonempty),
  positions $i+1..a$ are $\mathsf{C}$ and position $a+1$ is a sign letter; hence the
  maximal $\{\mathsf{A},\mathsf{B}\}$-run from position 2 ends exactly at $i$, and the
  maximal $\mathsf{C}$-run from $i+1$ ends exactly at $a$: $\Psi$ recovers $(i, a)$.
  It then recovers $\varepsilon_2..\varepsilon_i$ and $\varepsilon_{a+1}$ directly;
  the block coordinates as $\overline{\varepsilon_{a+1}}$ — correct by Lemma 6(II) —
  and the tail as in case (I). By Lemma 5(II), $(a,i,\delta)$ determines $s$.

**4. $\Phi \circ \Psi = \mathrm{id}$.** Let $\sigma \in W_n$ and $(s,\varepsilon) =
\Psi(\sigma)$. In each branch, $\Phi$ applied to $\Psi$'s output writes back exactly
the letters read: (S) writes $\mathsf{A}$ then the sign letters; (I) writes the $a$
sign letters read from positions $1..a$, the $\mathsf{C}$ at $a+1$, and for $j \ge
a+2$ a $\mathsf{C}$ iff $\delta_j = 1$ iff $\sigma_j = \mathsf{C}$, else
$\ell(\varepsilon_j) = \sigma_j$; (II) likewise reproduces the leading $\mathsf{C}$,
the run structure (positions $2..i$, the block $i+1..a$, position $a+1$) and the tail.
So $\Phi(\Psi(\sigma)) = \sigma$.

By 3 and 4, $\Phi$ is a bijection with inverse $\Psi$. $\square$

---

## 9. Main theorem

**Theorem.** For all $n \ge 1$, the number of nonnesting permutations of $[n]_2$
avoiding $\{1132, 3312\}$ is
$$ c_n = 3^n - 3 \cdot 2^{n-1} + 1. $$

*Proof.* Compose the bijections:
$$ \{\text{avoiders}\}
   \;\xrightarrow{\;\text{Lemma 0 + Theorem A + Fact 3.1}\;}
   \{(s, \varepsilon) : \varepsilon \text{ valid for } s\}
   \;\xrightarrow{\;\Phi\ (\text{Theorem B})\;} W_n , $$
where the middle set ranges over all Dyck words $s$ — but by Lemmas 4 and 5 only
admissible $s$ (cases S/I/II of Lemma 5, which exhaust the shapes not excluded by
Lemma 4) carry valid sign words, so the middle set is exactly $\Phi$'s domain. By Lemma 7, $|W_n| = 3^n - 3\cdot 2^{n-1} + 1$. $\blacksquare$

The end-to-end map is explicit: given an avoider $w$, read off $(s, p)$ (Lemma 0),
convert $p$ to $\varepsilon$ (Fact 3.1), and write the string $\sigma$ (Definition of
$\Phi$); given $\sigma \in W_n$, parse it ($\Psi$), rebuild $s$ from the parameters
(Lemma 5), rebuild $p$ from $\varepsilon$ (Fact 3.1), and interleave (Lemma 0).

---

## 10. Worked examples

**$n = 3$: all 16 avoiders and their codes** (computed by `work/bij/verify_bijection.py`;
$\mathsf{A} = \mathsf{L}$, $\mathsf{B} = \mathsf{H}$):

| $\sigma$ | word | case | $\sigma$ | word | case |
|---|---|---|---|---|---|
| AAA | 321321 | S | ACB | 221133 | I, $a=1$ |
| AAB | 213213 | S | ACC | 221313 | I, $a=1$ |
| AAC | 323211 | I, $a=2$ | BAC | 232311 | I, $a=2$ |
| ABA | 231231 | S | BBC | 121233 | I, $a=2$ |
| ABB | 123123 | S | BCA | 223311 | I, $a=1$ |
| ABC | 212133 | I, $a=2$ | BCB | 112233 | I, $a=1$ |
| ACA | 332211 | I, $a=1$ | BCC | 223131 | I, $a=1$ |
| | | | CCA | 232131 | II |
| | | | CCB | 212313 | II |

Excluded strings ($3 \cdot 2^2 - 1 = 11$): $X_1 = \{BAA, BAB, BBA, BBB\}$,
$X_2 = \{CAA, CAB, CBA, CBB, CAC, CBC, CCC\}$.

**A case (II) example, $n = 6$.** $\sigma = \mathsf{CBCCAC}$. Parse: $\sigma_1 =
\mathsf{C}$; $\{\mathsf{A},\mathsf{B}\}$-run from position 2 is "$\mathsf{B}$", so
$i = 2$ and $\varepsilon_2 = \mathsf{H}$; $\mathsf{C}$-run occupies positions $3..4$,
so $a = 4$; $\varepsilon_5 = \ell^{-1}(\mathsf{A}) = \mathsf{L}$; block
$\varepsilon_3 = \varepsilon_4 = \overline{\mathsf{L}} = \mathsf{H}$; tail arc 6 has
$\sigma_6 = \mathsf{C}$: $\delta_6 = 1$, $\varepsilon_6 = \overline{\varepsilon_5}
= \mathsf{H}$. Shape: $s = U^4 D^2 U D^2 \cdot (D^{1+1-1} U) \cdot D^{1+1}
= UUUUDDUDDUDD$. Sign word $(\mathsf{H},\mathsf{H},\mathsf{H},\mathsf{L},\mathsf{H})$
gives $p = (2,3,4,5,1,6)$ (Fact 3.1: $p_1 = 1 + \#\mathsf{L} = 2$). Interleaving:
$$ w = 2\,3\,4\,5\,2\,3\,1\,4\,5\,6\,1\,6. $$
One checks directly that $w$ is nonnesting and avoids $1132$ and $3312$ (it is in the
$n=6$ avoider list), and $\Phi(w) = \mathsf{CBCCAC}$.

---

## 11. Numeric validation log

All new tests are in `../work/bij/verify_bijection.py` (Python 3.11); avoider lists in
`../explore/avoiders_n{1..10}.txt` were produced by the pruned-DFS generator
`../explore/gen.py`, whose incremental criterion is the fast check of
`../data/enumerator.py` (itself validated against the literal containment definition —
`data/validation.json`, V1).

| Claim | Test | Range | Result |
|---|---|---|---|
| ground truth | avoider lists vs. independent brute force from the LITERAL containment definition | $n \le 5$ (all words of $[n]_2$) | T1 OK |
| ground truth | avoider lists vs. fast-check enumeration over all $n!\,\mathrm{Cat}_n$ pairs $(s,p)$ | $n \le 7$ | T1 OK |
| ground truth | counts vs. $3^n - 3\cdot2^{n-1}+1$ (and vs. Rust + Codex clean-room enumerations, recorded in `data/validation.json`) | $n \le 10$ (resp. $\le 8$) | T1 OK |
| $\Phi$ well-defined | every structural assert (FIFO; prefix-interval; $\le 1$ gap opener; tail heights $\le 1$; block constancy; forced-sign equalities $\varepsilon_j = \overline{\varepsilon_{j-1}}$; case shapes) on every avoider | $n \le 10$, all $85{,}514$ avoiders | T2 OK |
| $\Phi$ injective, image $\subseteq W_n$ | direct check; membership via the bullet predicate AND independently via the complement description $X_1 \cup X_2$ (the two agree on every string of the cube) | $n \le 10$, full $3^n$ cube | T3/T6 OK |
| $\Psi$ total on $W_n$; image are avoiders; $\Phi \circ \Psi = \mathrm{id}$ | parse every $\sigma \in W_n$, rebuild the word, verify avoidance with the validated fast checks, re-encode | $n \le 10$, all $\sigma \in W_n$ | T4 OK |
| image$(\Phi) = W_n$ | set equality | $n \le 10$ | T5 OK |
| $|W_n|$ | enumeration vs. formula; disjointness arithmetic | $n \le 10$; identity check $n \le 300$ | T6 OK |
| Theorem A | predicate $\equiv$ brute-force avoidance, pair by pair (sibling draft's test) | all pairs, $n \le 7$; per-shape counts vs. Rust at $n=8$ | `work/verify_draft.py`, `work/verify_theoremA.py` OK |

The $n = 9, 10$ avoider lists (18,916 and 57,514 words) were generated by a method
(pruned DFS) entirely independent of the shape classification and of the bijection,
so T2–T5 at $n = 9, 10$ are genuine tests of every structural lemma above, beyond the
$n \le 8$ range quoted in the paper.

## 12. Remarks

1. **Where $3^n - 3\cdot 2^{n-1} + 1$ comes from, bijectively.** Each position
   $j \ge 2$ of $\sigma$ is a three-way choice for arc $j$ — "new low"
   ($\mathsf{A}$), "new high" ($\mathsf{B}$), or "sign forced by the structure"
   ($\mathsf{C}$) — while position 1 absorbs the case distinction. The two excluded
   families are exactly the codes that would describe nothing: $X_1$ (a $\mathsf{C}$-free
   code must describe the staircase, whose first letter carries no information — the
   choice $\mathsf{B}$ is redundant), and $X_2$ (a leading $\mathsf{C}$ promises a gap
   opener, which forces a nonempty constant block *and* a subsequent free arc; codes
   $\mathsf{C}\,v\,\mathsf{C}^k$ lack one or the other).
2. **Why a letter-aligned encoding cannot be "pure".** From the staircase state there
   are six admissible continuations (extend the staircase with a free sign: 2; end it
   at a height-0 tail opener with a free sign: 2; end it at a gap opener whose block
   absorbs a free sign: 2), so no alignment of one ternary letter per arc can be
   injective; the one-slot shift in case (I) and the leading marker in case (II) are
   the minimal repair, and the $3\cdot 2^{n-1} - 1$ excluded strings are exactly the
   cost of those markers.
3. **Lean notes.** All objects are words and finite tuples; $\Phi$ and $\Psi$ are
   structurally recursive letter-by-letter constructions; the only proofs by induction
   are the left-to-right recovery of forced coordinates (Corollary 6.1, Theorem B
   step 3) and standard prefix-counting facts (Fact 0.1, Lemma 3). No generating
   functions, no weighted automata, no graph theory.

## 13. Honest gap list

None known. Specifically:

- Every map is given explicitly in both directions, with the inverse identities proved
  pointwise (Theorem B, steps 3–4), not by counting.
- The case analysis in Lemma 5 / Theorem B is exhaustive and mutually exclusive at
  every branch (S / I / II, distinguished by $\mathsf{C} \notin \sigma$ /
  $\sigma_1 \ne \mathsf{C} \ni \sigma$ / $\sigma_1 = \mathsf{C}$).
- Edge cases handled in-proof and re-checked numerically: $n = 1$ ($W_1 =
  \{\mathsf{A}\}$, no special-casing needed); $a = 1$ in case (I) (exactly one sign
  letter before the $\mathsf{C}$, namely $\sigma_1 = \ell(\varepsilon_2)$);
  $a = n-1$ in case (I) ($\sigma = v\,\mathsf{C}$, empty tail) and in case (II)
  (empty tail); $i = 1$ in case (II) (empty $\{\mathsf{A},\mathsf{B}\}$-run);
  $i = a - 1$ (block of size 1); all-$\mathsf{C}$ tails (chains of forced arcs).
- The foundation (Lemmas 0–2, Theorem A) is shared with `dyck-sign.md`, where it
  passed a hostile Codex review; the new sections (5–9) were verified end-to-end on
  every avoider for $n \le 10$ and every string of $\{\mathsf{A},\mathsf{B},
  \mathsf{C}\}^n$ for $n \le 10$ (T2–T6).
- Codex hostile review of this draft: see Section 14.

## 14. Codex referee report

Independent hostile review by Codex (GPT-5.5, xhigh reasoning, thread
`019eb9fb-5cb8-70c3-9fed-d5c11b3ea66d`, June 2026), instructed to find a gap or a
counterexample, with full shell access. Verdict (verbatim): **"VERDICT: CORRECT WITH
MINOR FIXES (items 1-6 above)"**, preceded by **"No counterexample found. The proof
survives the hostile pass. … No mathematical break found. The bijection and inverse
parse are airtight modulo these prose/formalization cleanups."**

Codex additionally ran a clean-room checker (written by itself, not reusing this
project's helper code) verifying through $n \le 6$: Theorem A against the literal
$1132/3312$ definitions, Lemma 2 (prefix-interval necessity) over arbitrary label
permutations, the admissible-shape classification, $\Phi/\Psi$, and
$\mathrm{image}(\Phi) = W_n$. It also re-ran `verify_bijection.py` (passing at the
depths it ran; the $n \ge 7$ runs timed out in its sandbox only — they pass here, see
Section 11).

Its six findings, all prose/formalization-level, are incorporated in this version:
(1) a wrong lemma cross-reference in the introduction (Lemma 6 → Lemma 7);
(2) $\mathrm{Tail}$'s side condition $d_1 \le h_0$ now explicitly conditional on
$m \ge 1$ (case (II) uses $\mathrm{Tail}(1;\,)$);
(3) the empty-interval convention for $\{u..v\}$ with $u > v$ is now declared
(Section 0);
(4) "(equivalently … an avoider)" reworded — a pair $(s,\varepsilon)$ *corresponds*
to an avoider, it is not one;
(5) the inference "$\exists$ a $\mathsf{C}$ at position $\ge 2$ followed later by a
non-$\mathsf{C}$ $\Rightarrow$ the first $\mathsf{C}$-run ends before position $n$"
in Theorem B's parse is now written out with the two-case argument;
(6) the main theorem now cites Lemmas 4 *and* 5 for the exhaustiveness of $\Phi$'s
domain.
