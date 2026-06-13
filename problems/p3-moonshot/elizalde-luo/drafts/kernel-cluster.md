# The Elizalde–Luo conjecture for {1132, 3312}: a generating-function proof (FIFO sign-queue / cluster decomposition)

**Statement proved.** For every $n \ge 1$, the number of nonnesting permutations of the
multiset $[n]_2 = \{1,1,2,2,\dots,n,n\}$ that avoid the patterns $1132$ and $3312$
(Elizalde–Luo conventions, pinned in `../DEFINITIONS.md` and restated in §0) equals
$$ a_n \;=\; 3^n - 3\cdot 2^{\,n-1} + 1 . $$

**Method (this draft's line of attack).** Reduce the problem to counting pairs
(Dyck word, sign vector) accepted by a *FIFO sign-queue automaton*: nonnesting forces the
open letters to close in first-opened–first-closed (queue) order, and the two forbidden
patterns translate into the rule *"a letter opened after the first closure must carry the
sign opposite to the common sign of all currently open letters."* The accepted pairs are
then counted by a generating function: unique factorization of the Dyck word into
irreducible components (the "cluster" decomposition), an exact classification of the
components with nonzero weight, and elementary geometric-series algebra produce the
rational ordinary generating function
$$ A(x) \;=\; \sum_{n\ge 1} a_n x^n
   \;=\; \frac{x\,(1-2x+3x^2)}{(1-x)(1-2x)(1-3x)}
   \;=\; \frac{3x}{1-3x} - \frac{3x}{1-2x} + \frac{x}{1-x}, $$
whence $a_n = 3^n - 3\cdot 2^{n-1} + 1$ and $a_n = 6a_{n-1} - 11a_{n-2} + 6a_{n-3}$
($n \ge 4$).

Every lemma is proved in full below, and every lemma was additionally machine-verified
against the project's vetted ground-truth enumerations (validation log in §11; the
verification driver is `../work/kc/verify_kc.py`). The proof is elementary throughout
(explicit bijections, finite case analyses, formal power series with rational closed
forms) and is designed to be Lean-formalizable.

---

## 0. Conventions

* A **word** is $w = w_1 \cdots w_{2n}$ over $\{1,\dots,n\}$ using each letter exactly
  twice (a permutation of $[n]_2$). No quotient by relabeling is taken
  (DEFINITIONS.md §5).
* **Containment** (biconditional convention): $w$ contains $\sigma = \sigma_1\cdots\sigma_k$
  iff there are indices $i_1 < \cdots < i_k$ with
  $w_{i_r} < w_{i_s} \Leftrightarrow \sigma_r < \sigma_s$ **and**
  $w_{i_r} = w_{i_s} \Leftrightarrow \sigma_r = \sigma_s$ for all $r,s$;
  $w$ **avoids** $\sigma$ otherwise.
* $w$ is **nonnesting** iff it avoids $1221$ and $2112$, i.e. there are no
  $i_1<i_2<i_3<i_4$ with $w_{i_1}=w_{i_4} \ne w_{i_2}=w_{i_3}$.
* For a value $v$, $o(v) < c(v)$ denote the positions of its first and second occurrence
  (its **opener** and **closer**).
* A **Dyck word** of length $2n$ is $s \in \{\mathrm U,\mathrm D\}^{2n}$ with $n$ U's,
  $n$ D's, every prefix having $\#\mathrm U \ge \#\mathrm D$. The **height** after a
  prefix is $\#\mathrm U - \#\mathrm D$ in that prefix. **Arc $i$** of $s$ is the pair
  (position of the $i$-th U, position of the $i$-th D), written $(o_i, c_i)$; so
  $o_1 < \cdots < o_n$ and $c_1 < \cdots < c_n$.
* For permutations (distinct letters) the patterns $132$, $312$ have their classical
  meaning, which coincides with the biconditional convention.
* $a_n := \#\{\,w$ nonnesting permutation of $[n]_2$ avoiding $1132$ and $3312\,\}$.

**Fact 0.1.** In a Dyck word, $o_i < c_i$ for every $i$.
*Proof.* The prefix ending at the $i$-th D contains $i$ D's, hence at least $i$ U's by
prefix-dominance; so the $i$-th U occurs at position $\le c_i$, and the positions
differ. $\square$

**Fact 0.2 (open arcs).** Fix a Dyck word $s$ and an arc $j$, and let
$b_j := \#\{i : c_i < o_j\}$ (the number of D's preceding the $j$-th U). The arcs that
are *open* just before position $o_j$ (opened but not yet closed) are exactly
$$ \mathrm{Open}(j) \;=\; \{\, b_j + 1,\; b_j + 2,\; \dots,\; j-1 \,\}. $$
*Proof.* The arcs opened before $o_j$ are exactly $1,\dots,j-1$ (the U's are numbered in
position order). The arcs closed before $o_j$ are those $i$ with $c_i < o_j$; since
$c_1 < c_2 < \cdots$, these are exactly $1,\dots,b_j$. Each closed-before-$o_j$ arc is
also opened before $o_j$ (Fact 0.1), so $b_j \le j-1$. $\square$

**Fact 0.3 (crossing description).** For arcs $k < j$: $\;k \in \mathrm{Open}(j)$
$\iff$ $o_k < o_j < c_k$ $\iff$ $o_k < o_j < c_k < c_j$ (the arcs *cross*).
*Proof.* $k<j$ gives $o_k < o_j$ and $c_k < c_j$ automatically; "open at $o_j$" means
precisely $c_k > o_j$. $\square$

---

## 1. Normal form: nonnesting = Dyck shape × label permutation (FIFO)

**Lemma 1.** The map
$$ (s,p) \mapsto w(s,p) := \text{the word carrying letter } p_i
   \text{ at the } i\text{-th U and at the } i\text{-th D of } s $$
is a bijection from $\{\text{Dyck words of length } 2n\} \times S_n$ onto the set of
nonnesting permutations of $[n]_2$. Under it, the two occurrences of $p_i$ sit at
positions $o_i < c_i$. In particular the open letters of a nonnesting word always close
in first-opened–first-closed (FIFO/queue) order.

*Proof.* First, a reformulation of nonnesting. Say values $u \ne v$ **nest** in $w$ if
$o(u) < o(v) < c(v) < c(u)$.

(i) *$w$ contains $1221$ or $2112$ $\iff$ some two values nest.* If $u,v$ nest, the
subsequence of $w$ at positions $o(u), o(v), c(v), c(u)$ is $u\,v\,v\,u$ with $u \ne v$:
an occurrence of $1221$ (if $u<v$) or $2112$ (if $u>v$); the biconditional conditions
hold because the equal pattern letters are mapped to equal word letters and the unequal
ones to the distinct values $u \ne v$ in the right order. Conversely, an occurrence of
$1221$ or $2112$ at $i_1<i_2<i_3<i_4$ has $w_{i_1} = w_{i_4} = u$ and
$w_{i_2} = w_{i_3} = v$ with $u \ne v$; since every value occurs exactly twice,
$\{i_1,i_4\} = \{o(u), c(u)\}$ and $\{i_2,i_3\} = \{o(v),c(v)\}$, so
$o(u) < o(v) < c(v) < c(u)$: a nesting.

(ii) *No two values nest $\iff$ the sequence of values listed by opener position equals
the sequence listed by closer position.* If the sequences are equal then
$o(u) < o(v) \Rightarrow c(u) < c(v)$, which makes a nesting impossible. If they
differ, then the two linear orders on the $n$ values "by opener position" and "by
closer position" are distinct, so some pair of values is inverted between them (two
total orders on a finite set that agree on all pairs are equal): there are $u \ne v$
with $o(u) < o(v)$ and $c(v) < c(u)$. Together with $o(v) < c(v)$ (every value's opener
precedes its closer) this gives $o(u) < o(v) < c(v) < c(u)$, a nesting.

Now the bijection. *Well-definedness:* in $w(s,p)$ the letter $p_i$ occupies positions
$o_i < c_i$ (Fact 0.1), so first occurrences sit exactly at the U's; each letter is used
twice. *Image is nonnesting:* in $w(s,p)$ the opener sequence and the closer sequence
are both $p_1, \dots, p_n$, so by (i)–(ii) it is nonnesting. *Injectivity:* $s$ is the
first-occurrence indicator word of $w(s,p)$, and $p_i$ is the letter at the $i$-th U.
*Surjectivity:* given a nonnesting $w$, let $s(w)$ mark first occurrences U and second
occurrences D. Every prefix has $\#\mathrm D \le \#\mathrm U$ (each value closed in the
prefix was opened in it), so $s(w)$ is a Dyck word. By (i)–(ii) the value at the $i$-th
closer equals the value at the $i$-th opener; calling it $p_i$ defines a permutation
with $w = w(s(w), p)$. $\square$

From now on fix $n \ge 1$ and write $w = w(s,p)$.

---

## 2. The two patterns as suffix conditions

**Lemma 2.** Let $w$ be any permutation of $[n]_2$.
1. $w$ contains $1132$ $\iff$ there exist a value $a$ and positions
   $c(a) < t_1 < t_2$ with $w_{t_1} > w_{t_2} > a$.
2. $w$ contains $3312$ $\iff$ there exist a value $a$ and positions
   $c(a) < t_1 < t_2$ with $w_{t_1} < w_{t_2} < a$.

Consequently, $w$ avoids $\{1132, 3312\}$ $\iff$ for **every** value $a$, in the suffix
$w_{c(a)+1} \cdots w_{2n}$ the subsequence of letters $> a$ is weakly increasing and the
subsequence of letters $< a$ is weakly decreasing.

*Proof of 1.* ($\Rightarrow$) Let $i_1<i_2<i_3<i_4$ be an occurrence of $1132$: by the
biconditional convention $w_{i_1} = w_{i_2} = a$, and $w_{i_3} = c$, $w_{i_4} = b$ with
$a < b < c$. Since each value occurs exactly twice, $i_2 = c(a)$; take
$t_1 = i_3, t_2 = i_4$: then $c(a) < t_1 < t_2$ and $w_{t_1} = c > w_{t_2} = b > a$.
($\Leftarrow$) Given such $a, t_1, t_2$, the positions
$o(a) < c(a) < t_1 < t_2$ carry the letters $a, a, w_{t_1}, w_{t_2}$ with
$a < w_{t_2} < w_{t_1}$; this is an occurrence of $1132$ (the only equal pair of pattern
letters, positions 1–2, is mapped to the equal pair $a,a$; all other pairs are strictly
ordered as in $1132$). The proof of 2 is the mirror image ($a > w_{t_2} > w_{t_1}$,
pattern $3312$).

*Consequence.* "No pair $t_1 < t_2$ after $c(a)$ with $w_{t_1} > w_{t_2} > a$" says
exactly that the letters $> a$ in the suffix contain no strictly descending pair, i.e.
form a weakly increasing sequence (equal adjacent letters are allowed — the two copies of
one value); dually for letters $< a$. $\square$

---

## 3. Characterization of avoiders: P1 ∧ P2

For $w = w(s,p)$ define:

* **P1**: $p$ avoids $132$ and $312$;
* **P2**: for all arcs $i < k < j$ with $c_i < o_j < c_k$ (i.e. $i \le b_j$ and
  $k \in \mathrm{Open}(j)$, by Facts 0.2–0.3): $p_i$ lies strictly between $p_k$ and
  $p_j$.

We will use the following standard consequence of P1.

**Fact 3.1.** $p$ satisfies P1 $\iff$ for every $i$ and all $i < r < s$:
$p_r, p_s > p_i \Rightarrow p_r < p_s$, and $p_r, p_s < p_i \Rightarrow p_r > p_s$.
*Proof.* If $p_r > p_s > p_i$ with $i<r<s$, then $(i,r,s)$ is an occurrence of $132$;
if $p_r < p_s < p_i$, it is an occurrence of $312$. Conversely an occurrence of $132$
(resp. $312$) at $(i,r,s)$ violates the first (resp. second) implication. $\square$

**Lemma 3.** $w(s,p)$ avoids $\{1132, 3312\}$ $\iff$ P1 and P2 hold.

*Proof.* **($\Rightarrow$)** Suppose $w$ is an avoider.

*P1.* If $(i,k,l)$ is an occurrence of $132$ in $p$ ($i<k<l$, $p_i < p_l < p_k$), then
the closer positions satisfy $c_i < c_k < c_l$ and carry the letters $p_k, p_l$ at
$c_k < c_l$: a strictly descending pair of letters $> p_i$ after $c_i = c(p_i)$,
so $w$ contains $1132$ by Lemma 2 — contradiction. If $(i,k,l)$ is an occurrence of
$312$ ($p_k < p_l < p_i$), then the positions $c_k < c_l$ (both $> c_i$) carry the
ascent $p_k < p_l$ with both letters $< p_i$, so $w$ contains $3312$ — contradiction.

*P2.* Let $i<k<j$ with $c_i < o_j < c_k$ and suppose $p_i$ is **not** strictly between
$p_k$ and $p_j$; as $p$ is injective this means $p_k, p_j > p_i$ or $p_k, p_j < p_i$.
- If $p_k, p_j > p_i$: when $p_j > p_k$, the positions $o_j < c_k$ (both $> c_i$) carry
  the descent $p_j > p_k > p_i$; when $p_j < p_k$, the positions $c_k < c_j$ (both
  $> c_i$) carry the descent $p_k > p_j > p_i$. Either way Lemma 2 gives $1132$ —
  contradiction.
- If $p_k, p_j < p_i$: when $p_j < p_k$, positions $o_j < c_k$ carry the ascent
  $p_j < p_k < p_i$; when $p_j > p_k$, positions $c_k < c_j$ carry the ascent
  $p_k < p_j < p_i$. Either way $3312$ — contradiction.

**($\Leftarrow$)** Suppose P1 and P2 hold. By Lemma 2 it suffices to show, for every arc
$i$: any two positions $t_1 < t_2$, both $> c_i$, with letters $x_1, x_2$ both $> p_i$
satisfy $x_1 \le x_2$; and dually with both $< p_i$ and $x_1 \ge x_2$.

Each position $> c_i$ is either a closer $c_k$ with $k > i$, or an opener $o_j$ with
$o_j > c_i$ (which forces $j > i$, since $o_j > c_i > o_i$). Four cases for
$(t_1, t_2)$, letters $> p_i$ (the dual case is treated in brackets):

1. $(c_k, c_l)$, $k < l$, both $> i$: Fact 3.1 gives $p_k < p_l$ [resp. $p_k > p_l$].
2. $(o_j, o_{j'})$, $j < j'$, both $> i$: Fact 3.1 gives $p_j < p_{j'}$
   [resp. $p_j > p_{j'}$].
3. $(c_k, o_j)$ with $c_k < o_j$: then $o_j > c_k > o_k$, so $j > k$, and $i<k<j$;
   Fact 3.1 gives $p_k < p_j$ [resp. $p_k > p_j$].
4. $(o_j, c_k)$ with $o_j < c_k$:
   - $k = j$: equal letters, fine in the weak orders.
   - $k > j$: $i<j<k$ and Fact 3.1 gives $p_j < p_k$ [resp. $p_j > p_k$].
   - $k < j$: then $k \in \mathrm{Open}(j)$ (Fact 0.3: $k<j$, $o_j < c_k$) and
     $c_i < o_j$, i.e. $i \le b_j$, so $i < k < j$ falls under P2: $p_i$ is strictly
     between $p_k$ and $p_j$. This contradicts "$p_k, p_j$ both $> p_i$"
     [resp. both $< p_i$], so this sub-case **cannot occur** — there is nothing to
     check.

In all occurring cases the letters $> p_i$ ascend weakly and the letters $< p_i$ descend
weakly, so $w$ is an avoider. $\square$

---

## 4. Sign coordinates on Av(132, 312)

**Lemma 4.** Let $p \in S_n$.
1. $p$ avoids $\{132, 312\}$ $\iff$ every entry $p_m$ ($2 \le m \le n$) is either a
   strict prefix-maximum ($p_m = \max(p_1..p_m)$) or a strict prefix-minimum.
2. The map $p \mapsto \varepsilon(p) = (\varepsilon_2,\dots,\varepsilon_n)$,
   $\varepsilon_m := +1$ if $p_m$ is a prefix-maximum and $-1$ if a prefix-minimum, is a
   bijection from $\mathrm{Av}_n(132,312)$ onto $\{\pm 1\}^{n-1}$. In particular
   $|\mathrm{Av}_n(132,312)| = 2^{n-1}$.
3. *(Comparison fact.)* If $p \in \mathrm{Av}_n(132,312)$ and $1 \le i < k \le n$, then
   $$p_k > p_i \iff \varepsilon_k = +1 .$$

*Proof.* 1. ($\Leftarrow$) Suppose every entry is a prefix-min or prefix-max and $p$
contained $132$ at $i<k<l$ ($p_i < p_l < p_k$): then $p_l$ is not a prefix-min
($p_l > p_i$) and not a prefix-max ($p_l < p_k$), contradiction. A $312$ at $i<k<l$
($p_k < p_l < p_i$) makes $p_l$ neither a prefix-min ($p_l > p_k$) nor a prefix-max
($p_l < p_i$), contradiction. ($\Rightarrow$) If some $p_m$ ($m \ge 2$) is neither, pick
$i_0 < m$ with $p_{i_0} > p_m$ and $i_1 < m$ with $p_{i_1} < p_m$. If $i_1 < i_0$ then
$(i_1, i_0, m)$ is an occurrence of $132$; if $i_0 < i_1$ then $(i_0, i_1, m)$ is an
occurrence of $312$.

2. For $m \ge 2$, $p_m$ cannot be both prefix-min and prefix-max, so $\varepsilon(p)$ is
well defined. Observe that if $\varepsilon_m = +1$ then $p_m = \max(p_1..p_m) =
\max V_m$ where $V_m := \{p_1,\dots,p_m\}$, and dually. Decreasing induction on $m$
shows the following reconstruction is forced and always succeeds: starting from
$V_n = [n]$, for $m = n, n-1, \dots, 2$: $p_m = \max V_m$ if $\varepsilon_m = +1$,
$p_m = \min V_m$ if $\varepsilon_m = -1$, and $V_{m-1} = V_m \setminus \{p_m\}$;
finally $p_1$ is the last remaining value. Hence $\varepsilon$ is injective; and for any
prescribed $\varepsilon \in \{\pm1\}^{n-1}$ the same recipe constructs a permutation in
which every entry is by construction a prefix-extreme with the prescribed signs, proving
surjectivity (using part 1 to conclude it avoids $\{132,312\}$).

3. If $\varepsilon_k = +1$ then $p_k = \max(p_1..p_k) > p_i$; if $\varepsilon_k = -1$
then $p_k = \min(p_1..p_k) < p_i$. (Note $k \ge 2$ since $k > i \ge 1$.) $\square$

---

## 5. P2 as a sign-constraint system

For a Dyck word $s$ and a sign vector $\varepsilon = (\varepsilon_2,\dots,\varepsilon_n)$
define the constraint system
$$ E(s,\varepsilon): \qquad \text{for every arc } j \text{ with } b_j \ge 1
   \text{ and every } k \in \mathrm{Open}(j): \quad \varepsilon_k = -\varepsilon_j . $$
(All indices occurring here satisfy $k \ge b_j + 1 \ge 2$ and $j > k \ge 2$, so
$\varepsilon_1$ is never referenced; the system is well defined on
$(\varepsilon_2,\dots,\varepsilon_n)$.)

**Lemma 5.** Let $p \in \mathrm{Av}_n(132,312)$ with sign vector $\varepsilon$, and let
$s$ be a Dyck word. Then $\mathrm{P2}(s,p) \iff E(s,\varepsilon)$. Consequently, by
Lemmas 1, 3, 4:
$$ a_n \;=\; \sum_{s \text{ Dyck, } |s| = 2n}
   \#\{\varepsilon \in \{\pm1\}^{n-1} : E(s,\varepsilon)\}. $$

*Proof.* By Facts 0.2–0.3, the triples $(i,k,j)$ quantified in P2 are exactly: $j$ any
arc, $k \in \mathrm{Open}(j)$, $i \in \{1,\dots,b_j\}$ (then $i < k$ holds
automatically since $i \le b_j < b_j + 1 \le k$). For such a triple, by the comparison
fact (Lemma 4.3) applied twice (valid since $i < k$ and $i < j$):
$$ p_i \text{ strictly between } p_k, p_j
   \iff \big(p_k > p_i\big) \ne \big(p_j > p_i\big)
   \iff \varepsilon_k \ne \varepsilon_j
   \iff \varepsilon_k = -\varepsilon_j. $$
The right side does not depend on $i$; therefore "for all $i \le b_j$" collapses to the
existence condition $b_j \ge 1$. Hence P2 $\iff$ $E(s,\varepsilon)$.

The counting formula: by Lemma 1, avoiders correspond to pairs $(s,p)$; by Lemma 3 to
pairs with P1 ∧ P2; by Lemma 4.2 the P1-part is parametrized bijectively by
$\varepsilon \in \{\pm1\}^{n-1}$; by the equivalence just proved the P2-part becomes
$E(s,\varepsilon)$. $\square$

**Convention (dummy sign).** It is convenient to add an unconstrained variable
$\varepsilon_1 \in \{\pm 1\}$: let $\widehat E(s,\cdot)$ denote the same constraint
system on $\varepsilon \in \{\pm1\}^n$. Since $\varepsilon_1$ never occurs in any
constraint,
$$ T_n := \sum_{s} |\mathrm{Sol}\,\widehat E(s)| \;=\; 2\, a_n . $$

---

## 6. Queue semantics

**Lemma 6 (operational reading of $\widehat E$).** Fix $s$ and
$\varepsilon \in \{\pm1\}^n$. Scan $s$ left to right, maintaining the FIFO queue of open
arcs (a U enqueues the next arc at the back; a D dequeues the front — by Fact 0.2 the
dequeued arc is precisely the one that closes). Then $\widehat E(s,\varepsilon)$ holds
$\iff$ at every U-step that (a) occurs after at least one D-step and (b) finds the queue
nonempty, the signs of all queued arcs are equal — say to $\sigma$ — and the new arc's
sign is $-\sigma$.

*Proof.* At the U-step of arc $j$, condition (a) says $b_j \ge 1$ and the queue contents
are $\mathrm{Open}(j)$ (Fact 0.2). For a nonempty index set $S$, the conjunction
"$\varepsilon_k = -\varepsilon_j$ for all $k \in S$" is equivalent to "all
$(\varepsilon_k)_{k\in S}$ are equal to some $\sigma$ and $\varepsilon_j = -\sigma$".
If the queue is empty ($\mathrm{Open}(j) = \varnothing$) or $b_j = 0$, the system
imposes nothing at $j$, matching the operational rule. $\square$

We refer to a U-step with $b_j \ge 1$ and queue nonempty as a **constrained opening**;
all other openings (those before the first D, and those at an empty queue) are
**free**.

---

## 7. Cluster decomposition: factorization over irreducible components

Every nonempty Dyck word factors **uniquely** as $s = c^{(1)} c^{(2)} \cdots c^{(r)}$
($r \ge 1$) into **irreducible components**: the factors between consecutive returns of
the height to $0$. Each component is irreducible (positive height internally), and every
arc of $s$ has both endpoints inside a single component (at a height-0 boundary all
opened arcs have closed). Write $m_t$ for the number of arcs of $c^{(t)}$.

For an irreducible Dyck word $c$ with $m$ arcs define two solution counts, both over
$\varepsilon \in \{\pm 1\}^m$ (arcs renumbered $1..m$ within $c$, $b_j$ and
$\mathrm{Open}(j)$ computed within $c$):
$$ N(c) := \#\{\varepsilon : \forall j \text{ with } b_j \ge 1,\;
   \forall k \in \mathrm{Open}(j): \varepsilon_k = -\varepsilon_j\}, $$
$$ M(c) := \#\{\varepsilon : \forall j,\;
   \forall k \in \mathrm{Open}(j): \varepsilon_k = -\varepsilon_j\}. $$
($N$ keeps the "after the first D" guard; $M$ drops it.)

**Lemma 7.** For every nonempty Dyck word $s$ with components
$c^{(1)}, \dots, c^{(r)}$:
$$ |\mathrm{Sol}\,\widehat E(s)| \;=\; N\!\big(c^{(1)}\big) \cdot
   \prod_{t=2}^{r} M\!\big(c^{(t)}\big). $$

*Proof.* The variables $\varepsilon_1,\dots,\varepsilon_n$ are partitioned by the
components (each arc lies in one component). Each constraint of $\widehat E(s)$ couples
$j$ with some $k \in \mathrm{Open}(j)$; by Fact 0.3 arcs $k$ and $j$ overlap as position
intervals, hence lie in the same component. So the constraint set splits by component,
and the solution set is the product of the per-component solution sets. It remains to
identify the factors.

Let $j$ be an arc of component $t$, and note $\mathrm{Open}_s(j) =
\mathrm{Open}_{c^{(t)}}(j)$ (all open arcs lie in the same component as $j$).
For $t = 1$: $b_j(s) = b_j(c^{(1)})$ (all earlier closers lie in $c^{(1)}$), so the
restricted system is exactly the $N$-system of $c^{(1)}$.
For $t \ge 2$: component $c^{(1)}$ ends with a D before any arc of $c^{(t)}$ opens, so
$b_j(s) \ge 1$ holds for *every* $j$ in $c^{(t)}$; the guard disappears and the
restricted system is exactly the $M$-system of $c^{(t)}$. $\square$

---

## 8. Classification of the component weights

Throughout this section $c$ is an irreducible Dyck word with $m \ge 1$ arcs, scanned as
in Lemma 6. Call a sign vector *valid* (for the $M$- or $N$-system, as appropriate) if
it solves the system. Since $c$ is irreducible, the queue is nonempty at every moment
strictly between the first letter and the last letter.

**Lemma 8 (queue dynamics).** Consider a (portion of a) scan throughout which every
opening at a nonempty queue is constrained, and whose starting queue is one of the
forms
$$ \varnothing, \qquad \sigma^i \;(i \ge 1), \qquad \sigma^i(-\sigma) \;(i \ge 0) $$
(sign words, front on the left; $\sigma \in \{\pm1\}$). Then for every sign vector
valid on this portion, the queue remains within these forms, and the complete
transition table is:
* $\varnothing \xrightarrow{\mathrm U} (\tau)$ with $\tau$ free (no constraint at an
  empty queue);
* $\sigma^i \xrightarrow{\mathrm U} \sigma^i(-\sigma)$ ($i\ge1$; all-equal, sign
  forced), $\quad \sigma^i \xrightarrow{\mathrm D} \sigma^{i-1}$;
* $\sigma^i(-\sigma)$, $i \ge 1$: **no U is permitted** (the queue is not all-equal,
  so no sign choice satisfies the constraint);
  $\sigma^i(-\sigma) \xrightarrow{\mathrm D} \sigma^{i-1}(-\sigma)$;
* $(-\sigma) = \sigma^0(-\sigma) \xrightarrow{\mathrm U} (-\sigma, \sigma)$, which is
  again of the form $\tau^1(-\tau)$ with $\tau = -\sigma$;
  $(-\sigma) \xrightarrow{\mathrm D} \varnothing$.

*Proof.* Each bullet is immediate from the constrained-opening rule of Lemma 6 (an
opening at a nonempty queue requires the queue all-equal and appends the opposite
sign; a D pops the front). Induction along the portion keeps the queue inside the
listed forms. $\square$

**Lemma 9 ($M$-weights).** For irreducible $c$ with $m$ arcs:
$$ M(c) = \begin{cases} 2, & c = \mathrm U(\mathrm{UD})^{m-1}\mathrm D
   \text{ (the \emph{fan}; for } m=1 \text{ this is } \mathrm{UD}), \\
   0, & \text{otherwise.} \end{cases} $$

*Proof.* In the $M$-system every opening at a nonempty queue is constrained, and the
scan starts at $\varnothing$, so Lemma 8 applies to the whole scan. Starting from
$\varnothing$, the transition table closes on the three states $\varnothing$, $(\tau)$,
$(\tau,-\tau)$: U from $\varnothing$ gives $(\tau)$; U from $(\tau)$ gives
$(\tau,-\tau)$; D from $(\tau)$ gives $\varnothing$; D from $(\tau,-\tau)$ gives
$(-\tau)$, a one-element queue; and no U is permitted at $(\tau,-\tau)$. Hence in any
valid scan the height never exceeds $2$, and no U is performed at height $2$.

An irreducible Dyck word with maximum height $\le 2$ is exactly a fan: write
$c = \mathrm U\, \tilde c\, \mathrm D$ with $\tilde c$ a Dyck word of maximum height
$\le 1$; Dyck words of height $\le 1$ are exactly $(\mathrm{UD})^k$, $k \ge 0$
(induction on length: such a word is empty or starts UD), so
$c = \mathrm U (\mathrm{UD})^{m-1} \mathrm D$.

Hence $M(c) = 0$ unless $c$ is a fan: a non-fan irreducible $c$ has some U performed at
height $2$, i.e. at state $(\tau,-\tau)$, where no sign choice satisfies the constraint
— so no valid $\varepsilon$ exists. (Formally: take the first violating prefix; the
induction of Lemma 8 applies to all earlier steps.)

For the fan, the scan is forced: U from $\varnothing$ ($2$ choices $\tau$), then
alternately U from $(\tau')$ (sign forced to $-\tau'$) and D; every constraint is
satisfied by construction, and there were exactly $2$ free choices in total. So
$M(\text{fan}) = 2$. $\square$

**Lemma 10 ($N$-weights).** Let $c$ be irreducible with $m$ arcs and maximal initial
U-run of length $a \ge 1$ (so the $(a{+}1)$-st letter of $c$ is a D). Then:
1. If $c = \mathrm U^a \mathrm D^a$ (equivalently $m = a$): $N(c) = 2^a$.
2. If $c = \mathrm U^{a}\, \mathrm D^{k}\, \mathrm U\, \mathrm D^{a-k}\,
   (\mathrm{UD})^{j}\, \mathrm D$ with $a \ge 2$, $1 \le k \le a-1$, $j \ge 0$
   (so $m = a + 1 + j$): $N(c) = 2^{\,k+1}$.
3. For every other irreducible $c$: $N(c) = 0$.

*Proof.* In the $N$-system the guard $b_j \ge 1$ deactivates the constraints of exactly
the arcs $1, \dots, a$ (those opened before the first D — the first D of $c$ is the
letter following the maximal initial U-run); every arc $j > a$ has $b_j \ge 1$ and is
constrained.

**Case $m = a$.** Then $c = \mathrm U^a \mathrm D^a$ (no further U's) and there are no
constraints at all: $N = 2^a$. (This $c$ is irreducible, with internal heights
$\ge 1$.)

**Case $m > a$.** Let the $(a{+}1)$-st U occur after exactly $k$ D's. Then $k \ge 1$
(maximality of the initial run) and $k \le a - 1$ (height $a - k$ just before that U is
$\ge 1$, since an internal return to height 0 would contradict irreducibility). At that
U the queue is $(\varepsilon_{k+1}, \dots, \varepsilon_a)$ — by Fact 0.2,
$\mathrm{Open}(a{+}1) = \{k+1, \dots, a\}$, nonempty — and the constraint forces
$$ \varepsilon_{k+1} = \cdots = \varepsilon_a = \sigma \quad (\sigma \in \{\pm1\}
   \text{ free}), \qquad \varepsilon_{a+1} = -\sigma, $$
while $\varepsilon_1, \dots, \varepsilon_k$ remain completely free. The queue is now
$\sigma^{a-k}(-\sigma)$.

From this point on **every** opening is constrained (all later arcs have $b_j \ge 1$;
the queue is nonempty until the end of the component by irreducibility, except possibly
at the very last step). By the dynamics of Lemma 8:
* while the queue is $\sigma^{i}(-\sigma)$ with $i \ge 1$, no U is permitted; D's bring
  it down to $(-\sigma)$ after exactly $a - k$ D's;
* at a one-element queue $(\tau)$, either a D ends the component (height 0 — by
  irreducibility this must be the final letter), or a U appends the forced sign
  $-\tau$, giving $(\tau, -\tau)$;
* at $(\tau,-\tau)$ only a D is permitted, giving $(-\tau)$.

Hence the suffix of $c$ after the prefix
$\mathrm U^a \mathrm D^k \mathrm U \mathrm D^{a-k}$ is forced to be of the form
$(\mathrm{UD})^{j}\,\mathrm D$ for some $j \ge 0$, every sign in it being forced; any
other continuation contains a U at a non-all-equal queue and admits no valid sign
vector. Conversely, for $c$ exactly of this form, the construction above produces
exactly the valid sign vectors, with free choices $\varepsilon_1, \dots, \varepsilon_k$
and $\sigma$: $N(c) = 2^{k} \cdot 2 = 2^{k+1}$. (One checks the displayed words are
indeed irreducible Dyck words: the height profile is
$a \searrow a-k \nearrow a-k+1 \searrow 1 \;(\nearrow 2 \searrow 1)^{j} \searrow 0$,
positive internally.) $\square$

*(Machine check: Lemmas 7–10 were verified for every irreducible component with up to
9 arcs by brute force over all $2^m$ sign vectors, and up to 12 arcs by an independent
parity-union-find solver; the per-shape product of Lemma 7 was verified against brute
solution counts for all Dyck words with $n \le 8$. See §11, T7–T8.)*

---

## 9. The generating function

Let
$$ F(x) := \sum_{c \text{ irreducible}} N(c)\, x^{m(c)}, \qquad
   G(x) := \sum_{c \text{ irreducible}} M(c)\, x^{m(c)} $$
(formal power series; finitely many irreducible $c$ per degree, and both series have
zero constant term).

**Lemma 11 (sequence/cluster assembly).**
$$ T(x) := \sum_{n \ge 1} T_n\, x^n \;=\; \frac{F(x)}{1 - G(x)} . $$

*Proof.* Unique factorization of nonempty Dyck words into irreducible components is a
bijection
$$ s \;\longleftrightarrow\; \big(c^{(1)}; (c^{(2)}, \dots, c^{(r)})\big), \qquad r\ge1, $$
between Dyck words and pairs (irreducible word, finite sequence of irreducible words);
degrees add. By Lemma 7 the weight $|\mathrm{Sol}\,\widehat E(s)|$ is the product
$N(c^{(1)}) \prod_{t \ge 2} M(c^{(t)})$. Summing,
$T(x) = F(x) \sum_{q \ge 0} G(x)^q = F(x)/(1 - G(x))$, an identity of formal power
series (the geometric series is summable since $G(0) = 0$; each coefficient on both
sides is a finite sum). $\square$

**Lemma 12 (the two series).**
$$ G(x) = \frac{2x}{1-x}, \qquad
   F(x) = \frac{2x}{1-2x} \;+\; \frac{1}{1-x}\left(\frac{8x^3}{1-2x}
        - \frac{4x^3}{1-x}\right). $$

*Proof.* $G$: by Lemma 9 the only contributions are the fans, one per $m \ge 1$, each
of weight 2: $G(x) = \sum_{m\ge1} 2x^m = 2x/(1-x)$.

$F$: by Lemma 10 the contributing shapes are
(i) $\mathrm U^a\mathrm D^a$ ($a \ge 1$), weight $2^a$, degree $a$; and
(ii) $\mathrm U^{a}\mathrm D^{k}\mathrm U\mathrm D^{a-k}(\mathrm{UD})^{j}\mathrm D$
($a \ge 2$, $1 \le k \le a-1$, $j \ge 0$), weight $2^{k+1}$, degree $a+1+j$. These
shapes are pairwise distinct: a word of family (i) contains no U after its first D,
while every word of family (ii) does, so the families are disjoint; within family (i)
the parameter $a$ is the length of the word's unique U-run; within family (ii) the
parameters are recovered uniquely from the run structure ($a =$ initial U-run length,
$k =$ first D-run length, $j =$ number of UD-blocks between the second U-run and the
final D). Hence
$$ F(x) = \sum_{a\ge1} 2^a x^a
 \;+\; \sum_{a\ge2} \sum_{k=1}^{a-1} \sum_{j\ge0} 2^{k+1} x^{a+1+j}. $$
The first sum is $2x/(1-2x)$. In the second, $\sum_{j\ge0} x^j = 1/(1-x)$ and
$\sum_{k=1}^{a-1} 2^{k+1} = 2^{a+1} - 4$, so it equals
$\frac{1}{1-x} \sum_{a \ge 2} (2^{a+1} - 4)\, x^{a+1}
 = \frac{1}{1-x}\left( \sum_{m \ge 3} 2^m x^m - 4\sum_{m\ge3} x^m \right)
 = \frac{1}{1-x}\left( \frac{8x^3}{1-2x} - \frac{4x^3}{1-x} \right)$. $\square$

**Theorem.** For all $n \ge 1$,
$$ a_n \;=\; 3^n - 3 \cdot 2^{\,n-1} + 1, $$
with ordinary generating function
$$ A(x) = \sum_{n\ge1} a_n x^n
 = \frac{x(1-2x+3x^2)}{(1-x)(1-2x)(1-3x)}
 = \frac{3x}{1-3x} - \frac{3x}{1-2x} + \frac{x}{1-x}, $$
and consequently $a_n = 6a_{n-1} - 11a_{n-2} + 6a_{n-3}$ for $n \ge 4$, with
$a_1 = 1$, $a_2 = 4$, $a_3 = 16$.

*Proof.* By Lemma 5 and the dummy-sign convention, $A(x) = \tfrac12 T(x)$. By Lemmas
11–12,
$$ 1 - G(x) = \frac{1-3x}{1-x}, \qquad
   A(x) = \frac{F(x)}{2} \cdot \frac{1-x}{1-3x}. $$
Compute $\tfrac12 F(x) (1-x)$ step by step:
$$ \frac{F(x)}{2} = \frac{x}{1-2x} + \frac{4x^3}{(1-x)(1-2x)} - \frac{2x^3}{(1-x)^2}, $$
$$ \frac{F(x)}{2}(1-x) = \frac{x(1-x)}{1-2x} + \frac{4x^3}{1-2x} - \frac{2x^3}{1-x}
 = \frac{x(1 - x + 4x^2)}{1-2x} - \frac{2x^3}{1-x}. $$
Over the common denominator $(1-x)(1-2x)$, the numerator is
$$ x\big[(1 - x + 4x^2)(1-x) - 2x^2(1-2x)\big]
 = x\big[1 - 2x + 5x^2 - 4x^3 - 2x^2 + 4x^3\big]
 = x(1 - 2x + 3x^2). $$
Hence
$$ A(x) = \frac{x(1-2x+3x^2)}{(1-x)(1-2x)(1-3x)}. $$
Partial fractions: one verifies the polynomial identity
$$ x(1-2x+3x^2) = 3x(1-x)(1-2x) \;-\; 3x(1-x)(1-3x) \;+\; x(1-2x)(1-3x) $$
(expand: $3(1-3x+2x^2) - 3(1-4x+3x^2) + (1-5x+6x^2) = 1 - 2x + 3x^2$), so
$$ A(x) = \frac{3x}{1-3x} - \frac{3x}{1-2x} + \frac{x}{1-x}, $$
and for $n \ge 1$,
$$ a_n = [x^n]A(x) = 3\cdot 3^{n-1} - 3 \cdot 2^{n-1} + 1 = 3^n - 3\cdot2^{n-1} + 1. $$
The recurrence follows since $(1-x)(1-2x)(1-3x) = 1 - 6x + 11x^2 - 6x^3$ annihilates
the coefficient sequence from $n = 4$ on (the numerator has degree $3$), and the initial
values come from the formula. $\square$

---

## 10. Appendix: the kernel-automaton formulation (independent cross-check)

The queue semantics of Lemma 6 can also be turned into a step-by-step walk with one
catalytic "height" parameter and one auxiliary parameter, which we used as an
independent machine validation of the entire chain Lemmas 6–12.

For a prefix of a scan with sign assignments, record the state
$(\delta, h, d)$: $\delta \in \{0,1\}$ is whether a D has occurred, $h$ is the queue
length, and $d$ is the *last-change index* of the queue's sign word
$q_1 q_2 \cdots q_h$ (front to back): $d := \max\{\,i : q_i \ne q_{i+1}\,\}$, with
$d := 0$ for an all-equal or empty queue.

**Proposition A.** $T_n$ equals the total weight of walks of length $2n$ from
$(0,0,0)$ to $(1,0,0)$ with steps
* U, $\delta = 0$: from $(0,0,0)$ to $(0,1,0)$ with weight 2; from $(0,h,d)$,
  $h \ge 1$, to $(0,h{+}1,d)$ (append the back sign) or to $(0,h{+}1,h)$ (append the
  opposite sign), each weight 1;
* U, $\delta = 1$: from $(1,0,0)$ to $(1,1,0)$ with weight 2; from $(1,h,0)$,
  $h \ge 1$, to $(1,h{+}1,h)$ with weight 1 (the forced opposite sign); **no** U-step
  exists from $(1,h,d)$ with $d \ge 1$;
* D: from $(\delta,h,d)$, $h \ge 1$, to $(1, h{-}1, \max(d{-}1,0))$, weight 1.

*Proof sketch (not needed for the Theorem).* The map sending a pair
$(s, \varepsilon) \in \mathrm{Sol}\,\widehat E$ to its state trajectory plus the branch
choices at the weighted steps (the sign $\tau$ at empty-queue U's; "same/opposite" at
$\delta=0$, $h\ge1$ U's) is a bijection onto weighted walks: the queue's sign word — and
hence $\varepsilon$ — is reconstructed left to right from the branch labels, because a
constrained opening (only legal at $d = 0$, by Lemma 6) appends the uniquely determined
opposite sign, and popping the front updates $d \mapsto \max(d-1,0)$. Validity of
$(s,\varepsilon)$ corresponds exactly to the walk never demanding the missing U-step at
$d \ge 1$, $\delta = 1$. $\square$

A dynamic program over these states confirms $T_n = 2\,(3^n - 3\cdot2^{n-1} + 1)$ for
all $n \le 40$ (§11, T11). The cluster decomposition of §§7–9 is precisely the
"first-return / macro-step" solution of this walk system; we proved the closed form
that the kernel method would extract from it, so no kernel computation is needed in the
formal chain. The walk DP serves as an end-to-end numeric check that is independent of
the component classification.

---

## 11. Numeric validation log

All checks live in `../work/kc/verify_kc.py` (driver; pass `--n7` for the optional
exhaustive $n=7$ run) and were run on 2026-06-11 against the vetted ground truth in
`../data/` and the raw avoider enumerations in `../explore/avoiders_n*.txt`
(whose line counts $18916$ for $n{=}9$ and $57514$ for $n{=}10$ themselves equal
$3^n - 3\cdot2^{n-1}+1$ — the formula's first machine confirmations beyond the paper's
$n \le 8$). Output: `../work/kc/verify_kc_report.json`, `../work/kc/verify_kc_n7.log`.

| # | claim tested | range | result |
|---|---|---|---|
| T1 | Lemma 2 suffix criterion $\equiv$ literal containment definition | all $[n]_2$-words $n\le4$; all 5040 nonnesting words $n=5$ | PASS |
| T2 | Lemma 1 FIFO criterion $\equiv$ literal 1221/2112 definition | all $[n]_2$-words $n\le5$ | PASS |
| T3 | Lemma 3: avoider $\iff$ P1 ∧ P2 | exhaustive over all $(s,p)$, $n\le7$ ($n=7$: 2 162 160 pairs; full `--n7` run logged in `verify_kc_n7.log`); random: 20000 pairs each at $n=8,9$, 10000 at $n=10$ | PASS |
| T4 | Lemma 4: class equality, sign bijection, comparison fact | all $p \in S_n$, $n\le8$ | PASS |
| T5 | Lemma 5: P2 $\iff E(s,\varepsilon)$ | exhaustive over (shape, signed perm), $n\le8$ (183040 pairs at $n=8$) | PASS |
| T6 | Lemma 6: $\widehat E \equiv$ operational queue scan | exhaustive over $(s,\varepsilon)\in$ Dyck $\times \{\pm\}^n$, $n\le8$ | PASS |
| T7 | Lemma 7 factorization $|\mathrm{Sol}\,\widehat E(s)| = N\prod M$ | every Dyck $s$, $n\le8$, against brute solution counts | PASS |
| T8 | Lemmas 9–10 closed forms for $M(c)$, $N(c)$ | every irreducible $c$: $m\le9$ by $2^m$ brute force, $m\le12$ by independent parity-union-find solver | PASS |
| T9 | per-shape count $N\prod M/2$ $\equiv$ ground-truth avoider tallies | $n\le8$ vs `refined_stats.json` (Rust enumerator); $n=9,10$ vs raw avoider files (all $\mathrm{Cat}_n$ shapes, incl. zero-count shapes); totals $=3^n-3\cdot2^{n-1}+1$ | PASS |
| T10 | Lemma 12 + Theorem algebra: $F$ closed form $=$ direct triple sum (deg $\le 25$) $=$ brute component sums ($m\le12$); $A(x) =$ product form $=$ target rational $=$ partial fractions; $[x^n]A$, $n\le40$ | exact (sympy + integer arithmetic) | PASS |
| T11 | Proposition A walk DP: $T_n = 2(3^n-3\cdot2^{n-1}+1)$ | $n \le 40$ | PASS |
| T12 | avoider files: every listed word is FIFO and satisfies P1 ∧ P2 | all 18916 ($n=9$) + 57514 ($n=10$) words | PASS |

Prior, independently produced validations (other drafts in this folder, same ground
truth): exhaustive avoider $\iff$ P1∧P2 at $n=7$, per-shape formula at $n\le8$, and the
clean-room Codex enumerator cross-check recorded in `../data/validation.json`.

---

## 12. Honest gap list / audit notes

I believe the lemma chain above is complete and gap-free; every statement has a full
proof and an independent machine check. Points an auditor (or Lean formalization)
should scrutinize, and how they are addressed:

1. **Biconditional pattern convention** (equal pattern letters ↔ equal word letters).
   Used in Lemma 1(i) and Lemma 2; both directions of both lemmas spell out the
   equality/inequality checks. Machine-checked against the literal definition (T1, T2).
2. **Weak vs strict monotonicity in Lemma 2.** The two copies of a value may both
   appear in a suffix; only *strict* descents/ascents are forbidden, hence the weakly
   monotone formulation. The case $k=j$ in Lemma 3, case 4 handles exactly this.
3. **The vacuous case in Lemma 3 ($\Leftarrow$), case 4, $k<j$**: P2 *eliminates* the
   configuration rather than orienting it; the argument is "no such pair exists",
   not "the pair is ordered correctly".
4. **$\varepsilon_1$ is never constrained** (all constraints have $k \ge b_j+1 \ge 2$,
   $j > k$): this is why the dummy-variable convention with the clean factor 2 is
   legitimate. Checked implicitly by T5/T6 (exact equality of solution sets).
5. **Maximality of the initial run and irreducibility boundary cases in Lemma 10**
   ($k \ge 1$ from run-maximality, $k \le a-1$ from irreducibility; the final D of the
   component is the only point where the queue may empty). The classification was
   verified exhaustively for all irreducible shapes with $\le 12$ arcs (T8).
6. **No double counting in Lemma 12**: the three-parameter family is parametrized
   injectively by the run structure of the word; checked numerically by comparing the
   closed form of $F$ with brute-force component sums (T10).
7. **Formal-power-series hygiene in Lemma 11**: $G(0)=0$ makes $\sum_q G^q$ coefficient-
   wise finite; no analytic convergence is invoked anywhere.
8. The appendix Proposition A is *not* part of the proof chain (marked as such); its
   proof is sketched only, and it is used purely as an extra numeric cross-check.

**Status: no known gaps.** The result, with this chain, is a theorem modulo ordinary
human/machine refereeing; Codex (GPT-5.5) hostile review of this draft is recorded in
`../work/kc/codex_review_kc.md` and its objections are addressed in the text above
(see §13).

## 13. Referee round (Codex hostile review)

The completed draft was submitted to Codex (GPT-5.5, xhigh reasoning) with an
adversarial referee brief (find the gap / find the counterexample / recompute the
algebra; shell access granted for counterexample hunting). Full verbatim review and
disposition: `../work/kc/codex_review_kc.md` (thread
`019eb9eb-3563-7093-ad69-482af72bc1f1`).

**Verdict: ACCEPT-WITH-FIXES — "FATAL: none found. GAP: none found."** Codex
independently stress-tested Lemma 10's classification through 13 arcs (parity-DSU),
the Lemma 12 family-injectivity claim over a broad parameter range, the dummy-sign
factor-2 bookkeeping against direct $(s,p)$ counts through $n=6$, and the final
coefficient algebra; no failure appeared. Its three objections were presentational:

1. *(Lemma 12)* the family-(i)/(ii) discriminator was misphrased ("single maximal
   U-run") — fixed: the discriminator is "no U after the first D" vs. "some U after
   the first D", with the $(a,k,j)$ parameters recovered uniquely from the run
   structure.
2. *(Lemma 1)* the inversion-of-two-linear-orders step deserved an explicit
   justification — added.
3. *(§11)* the exhaustive $n=7$ T3 log was still being generated at review time — the
   run has since completed (PASS, 2 162 160 pairs) and is cited in the table.

All fixes are incorporated above.
