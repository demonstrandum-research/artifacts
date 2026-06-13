# Proof of the Elizalde–Luo conjecture for {1132, 3312}

**Statement.** For every $n \ge 1$, the number of nonnesting permutations of the
multiset $[n]_2 = \{1,1,2,2,\dots,n,n\}$ that avoid the patterns $1132$ and $3312$
equals
$$c_n(\{1132,3312\}) \;=\; 3^n - 3\cdot 2^{n-1} + 1 .$$

(Conjectured by Elizalde–Luo, *Pattern avoidance in nonnesting permutations*,
arXiv:2412.00336 / DMTCS 27:1 #13, Table 4. Conventions pinned in
`../DEFINITIONS.md`, quoted verbatim from the published LaTeX source
`../src/formatted.tex`.)

**Status: complete proof, no known gaps.** Every lemma below has been verified
numerically (see Section 8): the central characterization (Theorem A) exhaustively
at word level for all $2{,}162{,}160$ nonnesting words at $n=7$ and by a
set-equality argument at $n=8$; the shape-side classification and count
exhaustively over all $742{,}900$ Dyck shapes at $n=13$.

---

## 0. Conventions

A *word* $w = w_1 \cdots w_{2n}$ over $[n]_2$ uses each letter of $\{1,\dots,n\}$
exactly twice. For a value $v$, write $\mathrm{fst}(v) < \mathrm{snd}(v)$ for the
positions of its two occurrences.

*Containment* (Elizalde–Luo, biconditional convention): $w$ contains a pattern
$\sigma_1\cdots\sigma_k$ iff there are positions $i_1 < \cdots < i_k$ with
$w_{i_r} < w_{i_s} \Leftrightarrow \sigma_r < \sigma_s$ and
$w_{i_r} = w_{i_s} \Leftrightarrow \sigma_r = \sigma_s$ for all $r,s$.

*Nonnesting*: $w$ avoids $1221$ and $2112$; equivalently (containment convention
unwound, using that each value occurs exactly twice) there are **no two values
$u \ne v$ with $\mathrm{fst}(u) < \mathrm{fst}(v) < \mathrm{snd}(v) < \mathrm{snd}(u)$**.
(An occurrence of $1221$ or $2112$ at $i_1<i_2<i_3<i_4$ has
$w_{i_1} = w_{i_4} \neq w_{i_2} = w_{i_3}$; since each value has exactly two
copies, $\{i_1,i_4\}$ and $\{i_2,i_3\}$ are exactly the occurrence pairs of two
values $u,v$, nested as displayed. Conversely any such nested pair of values is an
occurrence of $1221$ (if $u<v$) or $2112$ (if $u>v$).)

Counting is over raw words; no quotient by relabeling is taken (DEFINITIONS.md §5).

Throughout, "$x$ strictly between $y$ and $z$" means $y < x < z$ or $z < x < y$.

---

## 1. Nonnesting words = Dyck shape × label permutation

For any word $w$ over $[n]_2$, mark each first occurrence U (*opener*) and each
second occurrence D (*closer*). Every prefix has at least as many U's as D's (each
closer is preceded by its own opener), so the U/D-sequence $s = s(w)$ is a Dyck
path with $n$ U's and $n$ D's. Let $o_1 < \cdots < o_n$ be the opener positions
and $q_1 < \cdots < q_n$ the closer positions. In any Dyck path $o_i < q_i$ for
all $i$ (the $i$-th U precedes the $i$-th D, since every prefix has
$\#U \ge \#D$).

**Lemma 0.** *A word $w$ over $[n]_2$ is nonnesting iff for every $i \in [n]$ the
letter at the $i$-th opener equals the letter at the $i$-th closer.*

*Proof.* The occurrence pairs $(\mathrm{fst}(v), \mathrm{snd}(v))$ form a perfect
matching of $[2n]$ pairing each opener to a closer; write $\sigma \in S_n$ for the
permutation with $\mathrm{fst}$-position $o_i$ matched to $q_{\sigma(i)}$.

($\Leftarrow$) If $\sigma = \mathrm{id}$, suppose values $u \neq v$ nest:
$\mathrm{fst}(u) < \mathrm{fst}(v)$ and $\mathrm{snd}(v) < \mathrm{snd}(u)$. The
first inequality says $u$'s opener index is smaller, i.e. $u = p_i, v = p_j$ with
$i < j$; but then $\mathrm{snd}(u) = q_i < q_j = \mathrm{snd}(v)$, a
contradiction.

($\Rightarrow$) If $\sigma \neq \mathrm{id}$, pick $i < j$ with
$\sigma(i) > \sigma(j)$. The value opened at $o_j$ has
$o_i < o_j < q_{\sigma(j)} < q_{\sigma(i)}$ (using $o_j < q_{\sigma(j)}$, valid
for every matched pair), so it nests inside the value opened at $o_i$:
$w$ is nesting. $\square$

Hence the map $w \mapsto (s, p)$, where $p_i := w_{o_i}$, is a **bijection**
between nonnesting words of $[n]_2$ and pairs (Dyck path $s$ of semilength $n$,
permutation $p \in S_n$): given $(s,p)$, place $p_i$ at the $i$-th U and at the
$i$-th D of $s$. (Both maps are inverse to each other by construction; in the
reconstructed word the two occurrences of $p_i$ are at $o_i < q_i$, so its opener
list and labels are recovered.) This recovers $|\mathcal C_n| = C_n \cdot n!$.

We call $i$ the *arc* with endpoints $(o_i, q_i)$ and label $p_i$. For $i < j$,
arcs $i,j$ are *crossing* if $o_j < q_i$ and *disjoint* if $q_i < o_j$
(nesting cannot occur). Note: **arc $i$ has no letters at positions $> q_i$**,
and every position $> q_i$ carries a letter of an arc $J > i$ (arc $J$'s last
position is $q_J$, and $q_J > q_i \Leftrightarrow J > i$).

---

## 2. Unwinding the patterns 1132 and 3312

**Lemma 1.** *Let $w$ be any word over $[n]_2$. Then:*
1. *$w$ contains $1132$ $\iff$ there are a value $a$ and positions
   $\mathrm{snd}(a) < k < l$ with $a < w_l < w_k$.*
2. *$w$ contains $3312$ $\iff$ there are a value $c$ and positions
   $\mathrm{snd}(c) < k < l$ with $w_k < w_l < c$.*

*Proof.* (1, $\Rightarrow$) Let $i_1<i_2<i_3<i_4$ be an occurrence of $1132$.
Then $w_{i_1} = w_{i_2} =: a$ (pattern letters $1,1$ are equal), so
$\{i_1,i_2\} = \{\mathrm{fst}(a), \mathrm{snd}(a)\}$ and $i_2 = \mathrm{snd}(a)$.
Take $k = i_3, l = i_4 > i_2$. The biconditional convention forces
$w_{i_3} > w_{i_4}$ (pattern $3 > 2$) and $w_{i_4} > w_{i_1} = a$ (pattern
$2 > 1$), i.e. $a < w_l < w_k$.

(1, $\Leftarrow$) The quadruple $(\mathrm{fst}(a), \mathrm{snd}(a), k, l)$ is
increasing and its letters $(a, a, w_k, w_l)$ satisfy exactly the order/equality
relations of $(1,1,3,2)$: the first two letters are equal and smaller than both
others, and $w_k > w_l$, with all stated inequalities strict. So it is an
occurrence of $1132$. Part (2) is the same argument with all inequalities
reversed above $c$. $\square$

**Lemma 2.** *$w$ avoids $\{1132, 3312\}$ $\iff$ there is **no** triple
$(v, x, y)$ with $v$ a value and $\mathrm{snd}(v) < x < y \le 2n$ such that $w_y$
is strictly between $v$ and $w_x$.*

*Proof.* "$w_y$ strictly between $v$ and $w_x$" means $v < w_y < w_x$ (a
$1132$-witness with $a = v$, by Lemma 1(1)) or $w_x < w_y < v$ (a
$3312$-witness with $c = v$, Lemma 1(2)). $\square$

---

## 3. The label permutation avoids {132, 312}

For a permutation $p$, an occurrence of (classical) $132$ is $i<j<k$ with
$p_i < p_k < p_j$; of $312$, $i<j<k$ with $p_j < p_k < p_i$. Both together:
$p_k$ strictly between $p_i$ and $p_j$ for some $i,j < k$ (in either index
order).

**Lemma 3.** *Let $w = (s,p)$ be nonnesting. If $w$ avoids $\{1132,3312\}$ then
$p$ avoids $\{132, 312\}$. Conversely, if $p$ contains $132$ or $312$, then $w$
contains $1132$ or $3312$.*

*Proof.* Suppose $i<j<k$ with $p_k$ strictly between $p_i$ and $p_j$. The
positions $q_i < q_j < q_k$ carry the letters $p_i$ (at $\mathrm{snd}(p_i)$),
$p_j$, $p_k$. Apply Lemma 2 with $(v,x,y) = (p_i, q_j, q_k)$: $w_y = p_k$ is
strictly between $v = p_i$ and $w_x = p_j$, so $w$ contains a forbidden pattern.
Both statements follow. $\square$

**Lemma 4 (structure of $\mathrm{Av}(132,312)$).** *For $p \in S_n$ the following
are equivalent:*
1. *$p$ avoids $\{132, 312\}$;*
2. *every $p_k$ is the minimum or the maximum of $\{p_1, \dots, p_k\}$;*
3. *every prefix set $\{p_1,\dots,p_k\}$ is an interval of integers.*

*Moreover, the map $\Phi: p \mapsto \varepsilon = (\varepsilon_2,\dots,\varepsilon_n)
\in \{L,H\}^{n-1}$, where $\varepsilon_k = H$ if $p_k = \max\{p_1..p_k\}$ and
$\varepsilon_k = L$ if $p_k = \min\{p_1..p_k\}$, is a bijection
$\mathrm{Av}_n(132,312) \to \{L,H\}^{n-1}$, and for all $i < j$:*
$$p_i < p_j \iff \varepsilon_j = H. \tag{$\ast$}$$

*Proof.* (1)$\Rightarrow$(2): if $p_k$ is not extreme in its prefix, there are
$u, v < k$ with $p_u < p_k < p_v$; if $u<v$ then $(u,v,k)$ is an occurrence of
$132$, if $v<u$ then $(v,u,k)$ is an occurrence of $312$.

(2)$\Rightarrow$(3): if some prefix $\{p_1..p_k\}$ is not an interval, it omits a
value $g$ with $\min < g < \max$ of the prefix. Since $p$ is a permutation of
$[n]$, $g = p_l$ for some $l > k$; then $p_l$ is neither the min nor the max of
$\{p_1..p_l\}$ (the prefix of index $k$ already contains values on both sides),
contradicting (2).

(3)$\Rightarrow$(1): under (3) each $p_k \in \{\min - 1, \max + 1\}$ of the
interval $\{p_1..p_{k-1}\}$ (it is a new value extending the interval to a larger
interval), hence never strictly between two earlier values; so no occurrence of
$132$ or $312$ exists.

Bijection: given (3), $\varepsilon$ is well defined ($p_k$ extends the prefix
interval at the bottom, $\varepsilon_k = L$, or the top, $\varepsilon_k = H$).
Conversely, from $\varepsilon$, set $p_1 = 1 + \#\{j : \varepsilon_j = L\}$ and
iteratively $p_k = (\text{current min}) - 1$ or $(\text{current max}) + 1$
according to $\varepsilon_k$; this is the unique preimage, lands in $S_n$ (it
uses each value of $[n]$ once: the final prefix is an interval of length $n$
containing $[\,p_1 - \#L,\; p_1 + \#H\,] = [1, n]$), and the two maps are
mutually inverse by induction on $k$.

($\ast$): if $\varepsilon_j = H$ then $p_j = \max\{p_1..p_j\} > p_i$; if
$\varepsilon_j = L$ then $p_j = \min\{p_1..p_j\} < p_i$. $\square$

---

## 4. Theorem A: the crossing-coloring characterization

**Theorem A.** *Let $w = (s, p)$ be a nonnesting word with $p \in
\mathrm{Av}(132,312)$ and $\varepsilon = \Phi(p)$. Then $w$ avoids
$\{1132,3312\}$ if and only if*
$$(C):\qquad \varepsilon_K \ne \varepsilon_J \quad\text{for every pair } K < J
\text{ with } q_1 < o_J < q_K. $$
*Consequently, $w \mapsto (s(w), \Phi(p(w)))$ is a bijection from the set of
$\{1132,3312\}$-avoiding nonnesting words of $[n]_2$ onto the set of pairs
$(s, \varepsilon)$, $s$ a Dyck path of semilength $n$ and
$\varepsilon \in \{L,H\}^{n-1}$, satisfying $(C)$.*

Note the pairs in $(C)$ are crossing pairs ($o_J < q_K$ with $K<J$) whose later
arc opens after the **first** closer; and automatically $K \ge 2$ (if $K=1$ then
$o_J < q_1$, contradicting $q_1 < o_J$).

*Proof.* By Lemma 2, $w$ contains a forbidden pattern iff there is a triple
$(v, x, y)$, $v = p_i$ some arc $i$, positions $q_i < x < y$, with $w_y$ strictly
between $p_i$ and $w_x$. Let $J$ and $K$ be the arcs of the letters at $x$ and
$y$. As noted in Section 1, $J, K > i$; and $J \neq K$ (else $w_x = w_y$, not
strict betweenness).

**Case $K > J$.** Then $i, J < K$, so $p_i, p_J \in \{p_1, \dots, p_{K}\}$, and
by Lemma 4(2) $p_K = w_y$ is the min or max of that set — never strictly between
$p_i$ and $p_J$. No triple of this type exists.

**Case $K < J$ (so $i < K < J$).** Positions of arc $K$: $o_K < o_J$ and
$q_K < q_J$. Since $x$ is a letter of $J$ and $y > x$ a letter of $K$, the only
possibility is $x = o_J$, $y = q_K$, requiring $o_J < q_K$; and $x > q_i$ reads
$q_i < o_J$. For the betweenness: by ($\ast$), if $\varepsilon_J = H$ then
$p_J > p_i$ and $p_J > p_K$, so "$p_K$ strictly between" $\iff p_i < p_K \iff
\varepsilon_K = H$; if $\varepsilon_J = L$ then $p_J$ is below both and
betweenness $\iff p_K < p_i \iff \varepsilon_K = L$. In both cases:
betweenness $\iff \varepsilon_K = \varepsilon_J$.

So a violating triple exists iff there are arcs $i < K < J$ with
$q_i < o_J < q_K$ and $\varepsilon_K = \varepsilon_J$. Finally, for fixed
$K < J$: such an $i$ exists $\iff$ ($K \ge 2$ and $q_1 < o_J$) — indeed $q_1$ is
the smallest closer, so $i = 1 < K$ works whenever $q_1 < o_J$ and $K \ge 2$;
conversely $i \ge 1$ forces $q_1 \le q_i < o_J$ and $i < K$ forces $K \ge 2$.
And as noted, $K \ge 2$ is automatic from $q_1 < o_J < q_K$. Hence: $w$ contains
a forbidden pattern $\iff$ $(C)$ fails.

The bijection statement combines this with Lemma 3 (avoiders must have
$p \in \mathrm{Av}(132,312)$, so none are lost), Lemma 4 ($p \leftrightarrow
\varepsilon$ bijectively for each $s$), and Lemma 0 ($w \leftrightarrow (s,p)$
bijectively). For $n = 1$, $\varepsilon$ is the empty word and $(C)$ is vacuous;
the unique word $11$ is an avoider. $\square$

---

## 5. Counting the admissible colored shapes

By Theorem A,
$$c_n(\{1132,3312\}) \;=\; T(n) \;:=\; \sum_{s} N(s), \qquad
N(s) := \#\{\varepsilon \in \{L,H\}^{n-1} \text{ satisfying } (C)\},$$
summed over Dyck paths $s$ of semilength $n$.

### 5.1 Notation

Fix $s$. Let $a \ge 1$ be the length of the first ascent run, i.e.
$o_j = j$ for $j \le a$ and position $a + 1$ is a closer, so $q_1 = a+1$.
For $J > a$ we have $o_J \ge a+2 > q_1$; for $J \le a$, $o_J = J < q_1$. Hence
the pairs in $(C)$ are exactly indexed by $J > a$ and $K \in S_J$, where
$$S_J := \{K < J : o_J < q_K\} \qquad (J > a).$$
Since closers increase, $S_J = \{m_J, m_J + 1, \dots, J-1\}$ with
$m_J - 1 = \#\{i : q_i < o_J\}$; thus $|S_J| = J - m_J$ equals the height of $s$
just before position $o_J$ (number of arcs open at that moment), and $S_J$ is
exactly the set of arcs open at the moment $o_J$. Also $1 \notin S_J$.

Condition $(C)$ restated: **for every $J > a$ and every $K \in S_J$:
$\varepsilon_K \neq \varepsilon_J$.**

### 5.2 Which shapes admit a coloring

**Proposition F1.** *If $N(s) > 0$, then for every $J > a$: either $|S_J| \le 1$
or $S_J \subseteq \{2, \dots, a\}$.*

*Proof.* Suppose $|S_J| \ge 2$ and some element of $S_J$ exceeds $a$. Then we can
pick $K_1 < K_2$ in $S_J$ with $K_2 > a$ (take $K_2$ = any element $> a$ and
$K_1$ any other element if smaller; if the other element is larger, rename — the
larger of the two is still $> a$). Claim: $K_1 \in S_{K_2}$. Indeed
$K_1 < K_2$ and $q_{K_1} > o_J > o_{K_2}$ (the first since $K_1 \in S_J$, the
second since $K_2 < J$ gives $o_{K_2} < o_J$). Since $K_2 > a$, the pair
$(K_1, K_2)$ is in $(C)$, as are $(K_1, J)$ and $(K_2, J)$. Any $\varepsilon$
satisfying $(C)$ would need $\varepsilon_{K_1}, \varepsilon_{K_2},
\varepsilon_J$ pairwise distinct in $\{L, H\}$ — impossible. $\square$

**Proposition F2.** *If $N(s) > 0$, at most one opener lies strictly between
$q_1$ and $q_a$.*

*Proof.* Suppose $o_{J_1} < o_{J_2}$ both lie in $(q_1, q_a)$, so
$J_1, J_2 > a$. Then $a \in S_{J_2}$ (as $o_a = a < q_1 < o_{J_2} < q_a$) and
$J_1 \in S_{J_2}$ (as $o_{J_1} < o_{J_2}$ and
$q_{J_1} \ge q_{a+1} > q_a > o_{J_2}$, using $J_1 \ge a+1$). So $|S_{J_2}| \ge 2$
with the element $J_1 > a$; by Proposition F1, $N(s) = 0$. $\square$

**Proposition F3.** *If $N(s) > 0$, then every $J$ with $o_J > q_a$ has
$|S_J| \le 1$.*

*Proof.* If $K \in S_J$ then $q_K > o_J > q_a$, so $K > a$. Thus
$S_J \not\subseteq \{2..a\}$ unless empty; Proposition F1 gives $|S_J| \le 1$.
$\square$

**Canonical form.** Suppose $N(s) > 0$. The positions $q_1, \dots, q_a$ together
with the openers between them are constrained as follows: by F2 at most one
opener lies in $(q_1, q_a)$, and if it exists it is $o_{a+1}$ (openers are
ordered, and $o_{a+1}$ is the smallest opener $> q_1$); write $i :=$ number of
closers before it, so $1 \le i \le a-1$ (strict betweenness; this requires
$a \ge 2$). Therefore
$$s \;=\; \mathsf{U}^a\, \mathsf{D}^a\, \tau
\qquad\text{or}\qquad
s \;=\; \mathsf{U}^a\, \mathsf{D}^i\, \mathsf{U}\, \mathsf{D}^{a-i}\, \tau
\quad (1 \le i \le a-1),$$
where $\tau$ — the part of $s$ after position $q_a$ — is a $\{U,D\}$-path
starting at height $h_0 = 0$ (first form) or $h_0 = 1$ (second form: the
*bridge* arc $B = a+1$ is still open), ending at height $0$, never negative,
and in which, by F3, **every U-step starts at height $\le 1$** (the height
before an opener $o_J > q_a$ equals $|S_J|$). Conversely, every $s$ of this form
with such a $\tau$ is a Dyck path whose first ascent run is $a$ and whose data
$(a, \text{bridge?}, i, \tau)$ are recovered uniquely from $s$, so the
correspondence
$$s \;\longleftrightarrow\; (a, \,\varnothing \text{ or } i, \,\tau)$$
is a bijection onto shapes of canonical form. (Heights stay positive through
phase 1: after $\mathsf D^i$ the height is $a - i \ge 1$; the first run is
exactly $a$ because a D follows $\mathsf U^a$ in both forms.)

### 5.3 The exact count $N(s)$ for canonical shapes

Let $s$ be canonical, with tail $\tau$ containing $m$ U-steps; let
$z(\tau) := \#\{\text{U-steps of } \tau \text{ starting at height } 0\}$.
The constraints of $(C)$ are exactly:

- **Bridge constraint** (second form only): $S_B = \{i+1, \dots, a\}$
  ($m_B = i + 1$ since exactly $i$ closers precede $o_B$; all of
  $\{i+1..a\} \subset$ first run). The constraints
  $\{\varepsilon_K \ne \varepsilon_B : K \in S_B\}$ hold iff
  $\varepsilon_{i+1} = \cdots = \varepsilon_a = c$ for some $c \in \{L,H\}$ and
  $\varepsilon_B = \bar c$.
- **Tail constraints**: each tail opener $J$ (i.e. $o_J > q_a$) at height $1$
  has $S_J = \{K\}$ for a single $K$ (which satisfies $K > a$, by the proof of
  F3 — so $K$ is the bridge or an earlier tail arc), giving
  $\varepsilon_J = \overline{\varepsilon_K}$; each tail opener at height $0$ has
  $S_J = \emptyset$ — no constraint.
- **No other constraints**: first-run arcs $K \le a$ occur in some $S_J$ only
  for $J = B$ (tail openers have $S_J \cap [1,a] = \emptyset$ since
  $q_K \le q_a < o_J$ for $K \le a$), and arc $1$ in none.

Counting solutions $\varepsilon$ by assigning variables in the order
$\varepsilon_2, \dots, \varepsilon_n$: each first-run variable not in
$\{\varepsilon_{i+1},\dots,\varepsilon_a\}$ is free; the block
$\varepsilon_{i+1} = \cdots = \varepsilon_a$ contributes one free binary choice
$c$, and $\varepsilon_B = \bar c$ is then forced; each tail variable is forced
(height-1 opener) or free (height-0 opener). Every constraint of $(C)$ has been
used exactly once, and each forced variable is determined by strictly earlier
ones, so the assignments multiply:
$$N(s) \;=\;
\begin{cases}
2^{\,a-1}\cdot 2^{\,z(\tau)} & \text{no bridge},\\[2pt]
2^{\,i-1}\cdot 2\cdot 2^{\,z(\tau)} \;=\; 2^{\,i}\, 2^{\,z(\tau)}
& \text{bridge after } i \text{ closers}.
\end{cases}$$
In particular $N(s) \ge 1$, so **admissible = canonical**, completing the
classification.

### 5.4 Tail counting

For $m \ge 0$ and $h \in \{0, 1, 2\}$ let $f(m, h)$ be the sum of
$2^{z(\tau)}$ over all paths $\tau$ from height $h$ to height $0$, staying
$\ge 0$, with exactly $m$ U-steps, each U-step starting at height $\le 1$.
(The height of such a path never exceeds $2$, by induction along the path.)
First-step decomposition gives, for $m \ge 1$:
$$f(m,0) = 2 f(m-1, 1), \qquad
f(m,1) = f(m, 0) + f(m-1, 2), \qquad
f(m,2) = f(m,1),$$
(at height $0$ only U is possible and it carries weight $2$; at height $1$
either D — leaving $f(m,0)$ — or a weight-$1$ U to height $2$; at height $2$
only D), with $f(0,0) = 1$ (empty path), $f(0,1) = 1$ (the path $\mathsf D$),
$f(0,2) = 1$. By induction,
$$f(m,1) = 3^m \quad (m \ge 0), \qquad
f(m,0) = \begin{cases} 1, & m = 0,\\ 2 \cdot 3^{m-1}, & m \ge 1,\end{cases}$$
since $f(m,1) = 2f(m-1,1) + f(m-1,1) = 3 f(m-1,1)$ for $m \ge 1$.

### 5.5 The final summation

Summing $N(s)$ over canonical shapes via the bijection of §5.2 (no-bridge
shapes: $1 \le a \le n$, tail has $m = n - a$ U-steps, $h_0 = 0$; bridge
shapes: $2 \le a \le n-1$ — note $a \le n-1$ since the bridge uses one arc —
and $1 \le i \le a - 1$, tail has $m = n-a-1$ U-steps, $h_0 = 1$):
$$T(n) \;=\; \sum_{a=1}^{n} 2^{a-1} f(n-a, 0)
\;+\; \sum_{a=2}^{n-1} \Big(\sum_{i=1}^{a-1} 2^{i}\Big) f(n-a-1, 1)
\;=\; \Sigma_1 + \Sigma_2 .$$

Using $\sum_{i=1}^{a-1} 2^i = 2^a - 2$ and the closed forms of $f$:

*First sum.* The term $a = n$ gives $2^{n-1}$; for $a < n$,
$2^{a-1} f(n-a,0) = 2^{a} 3^{\,n-a-1}$. With the identity
$\sum_{a=1}^{m} 2^{a-1} 3^{m-a} = 3^m - 2^m$ (induction on $m$: both sides are
$0$ at $m=0$ and satisfy $g(m) = 3g(m-1) + 2^{m-1}$):
$$\Sigma_1 = 2^{n-1} + 2\sum_{a=1}^{n-1} 2^{a-1} 3^{(n-1)-a}
= 2^{n-1} + 2\big(3^{n-1} - 2^{n-1}\big).$$

*Second sum* (empty for $n \le 2$):
$$\Sigma_2 = \sum_{a=2}^{n-1} (2^a - 2)\, 3^{\,n-1-a}
= 2\Big[\big(3^{n-1} - 2^{n-1}\big) - 3^{n-2}\Big]
- 2 \cdot \frac{3^{n-2} - 1}{2}
= 3^{n-1} - 2^{n} + 1,$$
where we removed the $a=1$ term $3^{n-2}$ from the first identity and used
$\sum_{k=0}^{n-3} 3^k = (3^{n-2}-1)/2$. (For $n \in \{1,2\}$ the expression
$3^{n-1} - 2^n + 1$ also equals $0$, so the formula holds for all $n \ge 1$.)

*Total.*
$$T(n) = 2^{n-1} + 2\cdot 3^{n-1} - 2^{n} + 3^{n-1} - 2^{n} + 1
= 3^{n} + 2^{n-1} - 2^{n+1} + 1 = 3^n - 3 \cdot 2^{n-1} + 1 . $$

**Theorem.** $c_n(\{1132,3312\}) = 3^n - 3\cdot 2^{n-1} + 1$ for all $n \ge 1$.
$\blacksquare$

---

## 6. Worked example ($n = 3$)

Shape $\mathsf{UUDUDD}$ ($a = 2$; bridge $B = 3$ after $i = 1$ closer; empty
tail): constraint $\varepsilon_2 \neq \varepsilon_3$. Solutions
$\varepsilon \in \{LH, HL\}$, i.e. $p \in \{(2,1,3), (2,3,1)\}$. The word
pattern of this shape is $p_1\, p_2\, p_1\, p_3\, p_2\, p_3$, giving the two
avoiders $2\,1\,2\,3\,1\,3$ and $2\,3\,2\,1\,3\,1$. One checks directly that
both avoid $\{1132, 3312\}$ while the other four label permutations of this
shape fail (e.g. $p = (1,2,3)$ gives $1\,2\,1\,3\,2\,3$, which contains $1132$
as the subsequence $1\,1\,3\,2$ at positions $1,3,4,5$).
$N = 2 = 2^{i}\, 2^{z(\tau)} = 2^1 \cdot 2^0$. ✓

## 7. Remarks on the structure (why $3^n - 3\cdot2^{n-1} + 1$)

The three geometric scales are transparent in the decomposition: the tail
automaton (heights $0,1,2$ with weights $2,1$) has growth $3$; the first-run
prefix contributes powers of $2$; their convolution produces exactly
$3^n - 3\cdot 2^{n-1} + 1$ — matching A168583's o.g.f.
$x(1-2x+3x^2)/((1-x)(1-2x)(1-3x))$ (shifted), poles at $1, 1/2, 1/3$.

---

## 8. Numeric validation log

All scripts in `../work/`; ground-truth data in `../data/` (Python + Rust
enumerators, cross-validated against the literal pattern definitions and a
clean-room Codex implementation; see `../data/validation.json`).

| Check | Scope | Result |
|---|---|---|
| V1–V5 (`data/`) | fast pattern predicates vs literal definition; shape×perm construction vs literal 1221/2112 filter; totals $n!\,C_n$; formula $n \le 8$ | all pass (pre-existing ledger) |
| `explore2.py`/`explore3.py` | every avoider has interval-prefix labels (Lemma 3+4); per-shape $\varepsilon$-sets are affine subspaces | $n \le 6$, pass |
| `verify_theoremA.py` | **Theorem A, word level**: predicted avoider $\iff$ actual avoider for every (shape, permutation) pair | all $n \le 7$ (2,162,160 pairs at $n=7$), **0 mismatches** |
| `verify_theoremA.py` | per-shape counts $2^{\#\text{comp}}\cdot[\text{bipartite}]$ vs independent Rust per-shape counts | $n \le 8$ (1430 shapes at $n=8$), exact match, sums = formula |
| `verify_shapes.py` | S1: $\sum_s N(s) =$ formula; S2: bipartite $\iff$ canonical form; S3: constraint graph is a forest, $\#\text{comp} = (n-1) - \#\text{edges}$, edge count $= (a-i) + \#\{\text{height-1 tail openers}\}$ | $n \le 13$ (742,900 shapes at $n=13$), all pass |
| `verify_final.py` (1) | summation identity §5.5 as exact integer identity | $n \le 60$, pass |
| `verify_final.py` (3) | $f(m,h)$ closed form vs direct path DP | $m \le 39$, pass |
| `verify_final.py` (2) | **set equality at $n = 8$**: every predicted $(s,\varepsilon)$ avoider is a true avoider (word-level check of all 6178 predicted words) + per-shape counts match Rust ⇒ predicted set = actual set | pass |

The $n=8$ set-equality argument: "predicted $\subseteq$ actual" is checked word
by word, and $|\text{predicted}| = |\text{actual}|$ per shape (against the
independent Rust enumeration), hence the sets are equal — a full word-level
verification of Theorem A at $n = 8$ without enumerating $57{,}657{,}600$ words.

**Hostile referee round (Codex / GPT-5.5, thread
`019eb9bf-8396-7573-90da-5c0aec5743c6`, two iterations).** Outcome: *"No kill.
I still found no flaw, gap, or counterexample."* Codex independently:
- attacked every lemma and case split listed in §9 (no objections);
- wrote a clean-room Rust harness
  (`work/codex_review/adversarial_referee.rs`) implementing the literal
  pattern definitions from DEFINITIONS.md, and ran a **full exhaustive
  word-level check of Theorem A at $n = 8$: all $57{,}657{,}600$
  (shape, permutation) pairs, predicted = literal avoider status, 0
  mismatches** (6178 avoiders both ways);
- ran randomized counterexample hunts beyond the exhaustive range: at
  $n = 9, 10, 11$, $2{,}000{,}000$ uniform (Dyck shape, arbitrary permutation)
  samples each (0 mismatches; 20/4/0 avoiders found resp.), plus a stratified
  hunt with $2{,}000{,}000$ uniform (shape, $\mathrm{Av}(132,312)$-permutation)
  samples each ($30{,}566 / 13{,}413 / 5{,}689$ avoiders found, 0 mismatches);
- re-derived by hand the two subtlest quantifier steps (Theorem A's
  $\exists i$-elimination; $S_J = \{J-1\}$ with $J - 1 > a$ for height-1 tail
  openers — a sharpening of the draft's $S_J = \{K\}, K > a$);
- verified the §6 worked example (all six label permutations) and confirmed
  the conventions against the published LaTeX source (`src/formatted.tex`
  lines 119–124, 135, 1614).

## 9. Honest gap list

I know of **no gaps**. Points a referee should scrutinize, with their
resolutions:

1. *Lemma 1 uses that each value occurs exactly twice* (to identify the pattern
   letters "11"/"33" with the two copies of one value). This is exactly the
   $[n]_2$ setting; the biconditional containment convention is the paper's
   (DEFINITIONS.md §2, verified against the literal definition in V1).
2. *Theorem A's case analysis* covers all triples $(v,x,y)$: $v$ must be an arc
   label with both copies $\le q_i$; $x, y$ belong to arcs $J, K > i$; the case
   split $K > J$ / $K < J$ is exhaustive; within $K < J$ the position
   combinatorics ($x = o_J$, $y = q_K$) is forced. Verified exhaustively for
   $n \le 7$ and by set equality at $n = 8$.
3. *Proposition F1's pair selection*: from $|S_J| \ge 2$ with an element $> a$
   one can always select $K_1 < K_2 \in S_J$ with $K_2 > a$: if the witness
   $K^* > a$ is not the larger of the two chosen, the larger one is also $> a$.
4. *§5.3 product count*: the constraint hypergraph is triangular (each
   constraint binds a variable strictly later than the variables it depends
   on; no variable is bound twice) — this is where F1–F3 are used. Verified
   per-shape for $n \le 13$.
5. *Boundary cases*: $n = 1$ ($\varepsilon$ empty, $(C)$ vacuous), $a = n$ (no
   tail), bridge with empty tail ($n = a+1$, $\tau = \mathsf D$), $\Sigma_2$
   empty for $n \le 2$. All covered explicitly and confirmed numerically.

## 10. Notes for Lean formalization

- Everything is finite and decidable; no analysis, no generating functions.
  The proof uses only: words as functions $\mathrm{Fin}\ 2n \to \mathrm{Fin}\ n$,
  the bijections of Lemma 0/4/Theorem A (each with explicit maps in both
  directions), two strong-induction recurrences ($f(m,h)$), and geometric-sum
  algebra (`Finset.geom_sum_eq` or bare induction).
- Suggested statement form (subtraction-safe over ℕ):
  $\#\{\dots\} + 3\cdot 2^{n-1} = 3^n + 1$.
- The decomposition of §5.2 is a Σ-type:
  $(a : \mathbb N) \times (\text{option } i) \times (\text{tail path})$, with the
  tail paths themselves a Σ-type over $\{L,H\}$-like step lists; $N(s)$ becomes
  a `Finset.card` of a product of decidable constraints; the final sum is
  `Finset.sum` over the Σ-type with `card_sigma`/`card_bij`.
