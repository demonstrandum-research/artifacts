# Three observations on the proofs in "Strong Majority Edge-Coloring" (arXiv:2607.00212v1)

John Erlbacher (Independent Researcher) · erlbacher.research@gmail.com · 11 July 2026

This memo records three observations about the written proofs of arXiv:2607.00212v1, made while studying the paper closely in the course of a Lean 4 verification project on Theorem 2, together with a proposed repair for the third. (Our formal proof follows a different construction; the kernel-checked result certifies the statement of Theorem 2, not the paper's argument — the observations below concern the written argument itself.) All references are to the compiled numbering of v1: Theorem 2 (five colors), Theorem 4 (four colors for graphs with no vertices of degree 2 or 4), Remark 6, Claim 7 (bad colors), Claim 8 (balance of $c_4$), Remark 9 (the free color at degree five), Claim 10 (ear extension), and the reduction operations (R1)–(R5). Quotations are taken from the arXiv LaTeX source of v1, with ellipses marking omitted text. None of the observations affects the statements of Theorem 2 or Theorem 4: the first two have immediate corrections, and the third is closed by a short repair using only the paper's own tools, given in full in Section 3 below.

## 1. Theorem 4: the displayed per-vertex bound fails at degree one

The proof of Theorem 4 displays

> After deleting the auxiliary leaves, every vertex $v\in V(G)$ satisfies
> $$d_i(v)\le\left\lfloor \frac{d(v)}4\right\rfloor+1\le \frac{d(v)-1}2$$
> for each color $i\in[4]$, $d(v)\notin \{2,4\}$.

and the following sentence applies this bound at both endpoints of every edge:

> Hence, for every edge $uv\in E(G)$ and any color $i\in[4]$, the number of $i$-colored edges adjacent to $uv$ is at most $d_i(u)+d_i(v)\le\frac{d(u)+d(v)}{2}-1$, so the coloring is strong majority.

At $d(v)=1$ the second displayed inequality reads $1 \le 0$, and Theorem 4's hypotheses permit degree-one vertices (for instance $K_{1,3}$, which is admissible and in scope). The conclusion of Theorem 4 is unaffected, by the following one-sided count: for a leaf edge $uv$ with $d(u)=1$, every edge adjacent to $uv$ meets $\{u,v\}$ in exactly one vertex, and the $u$-side is empty (the only edge at $u$ is $uv$ itself); hence the number of $i$-colored adjacent edges is at most $d_i(v) - [c(uv)=i] \le d_i(v) \le \frac{d(v)-1}{2} = \frac{d(u)+d(v)}{2}-1$, using the displayed bound only at $v$, where $d(v) \notin \{1,2,4\}$ — while a $K_2$ component has an empty edge neighborhood and threshold 0. This is exactly the degree-one consideration that Remark 6 supplies for the five-color proof; the analogous sentence appears to be missing from the proof of Theorem 4.

## 2. Claim 10, Case $k=1$: a duplicated passage

In the proof of Claim 10, under "Case $k=1$", two consecutive paragraphs (source lines 301 and 303 of `strong_majority_edge_coloring.tex`) both begin

> Note that we have $uv\in E(H)$. If $e_0$ and $e_1$ are already strong majority colored, we are done.

and both end

> Note that by this procedure, no edge other than $e_0$ or $e_1$ will change its color.

The two paragraphs appear to duplicate the same argument: the first includes the opening reduction to $d_H(v)=3$ (or $d_H(u)=3$), which the second skips, and they reach the same conclusion by the same count. We checked the count itself and it is correct — at most three colors forbidden at the high-degree end by Claim 7, at most two by the strong-majority condition of $e_0$, with the chord color common to both sets whenever they are full, so at most four of five colors are excluded. The mathematics of Case $k=1$ is sound; the duplication is editorial only.

## 3. Undoing (R1): the case of a degree-five vertex carrying two loop ears

### 3.1 The configuration

Let $v$ be a vertex with $d_G(v)=5$ carrying two loop ears — for instance two triangles through $v$ (each loop ear has length at least 3 in a simple graph, and contributes two incidences at $v$) plus one further edge, say a pendant leaf. The resulting graph is connected, admissible, and not a cycle, and (R1) is the first operation applied, so the configuration is in scope. Two loop ears force degree at least 5, so degree exactly 5 with two loop ears is the unique multi-loop shape at degree 5, and three loop ears at a degree-five vertex are impossible (they would force degree at least 6).

### 3.2 The relevant text

(R1), forward direction:

> If $d_G(v)\neq 5$, attach two new leaves at $v$, restoring the contribution of $2$ that $B$ made to $d_G(v)$ ...; if $d_G(v)=5$, attach a single leaf to $v$, lowering $d_G(v)$ from $5$ to $4$.

Remark 9 acknowledges the two-loop possibility:

> Let $v$ be a vertex of $G$ with $d_G(v)=5$ processed by (R1) or (R2). Exactly one of these operations is applied at $v$ and it removes at most two loop ears in the case of (R1) ... Consequently, $d_{G_4}(v)=4$ and the four edges at $v$ carry four distinct colors under $c_4$.

The undo pass's entire treatment of the $d_G(v)=5$ case is:

> For $d_G(v)=5$, the single leaf was removed, so one terminal edge inherits its color, and the other is free: any choice keeps the balance at $v$, and the loop interior then extends as before.

### 3.3 Why the written text does not cover the configuration

The branch condition "$d_G(v)=5$" can be read against the original degree or against the current degree during exhaustive application; we examined both readings.

- **Original-degree reading.** Each of the two loop ears is processed with a single leaf, so $d_{G_1}(v) = 5 - 4 + 2 = 3$. Then Remark 9's conclusion "$d_{G_4}(v)=4$" does not hold (the degree is 3, and (R5) does not change it), so the four-distinct-colors property that the restoration steps rely on fails as stated.
- **Current-degree reading** (the only one consistent with Remark 9). The first loop ear is processed at current degree 5 with one leaf, leaving degree 4; the second at current degree $4 \neq 5$ with two leaves, leaving degree 4. Then $d_{G_1}(v)=4$ with **three** auxiliary leaves plus one genuine edge, and Remark 9's conclusion holds. But the undo sentence quoted above presupposes that exactly one leaf was attached and that two terminal incidences must be restored, whereas here three leaves must be deleted and **four** terminal incidences (two per loop) must be colored. The $d_G(v)\neq 5$ paragraph does not apply either, since it presupposes two leaves per ear.

We also checked Claims 7, 8, 10, Remark 9, and the (R2)–(R4) undo passes for an implicit treatment of this vertex; none applies ((R2) never fires at $v$: after the first (R1) step its current degree is 4). In addition, Remark 9's sentence "Exactly one of these operations is applied at $v$" does not hold under either reading in this configuration ((R1) applies twice, once per ear).

### 3.4 A repair using only the paper's tools

By Claim 8, $c_4$ is balanced at $v$, which at degree 4 with five colors gives $d_i(v) \le \lfloor 3/2 \rfloor = 1$: the four edges of $G_4$ at $v$ — the genuine edge and the three auxiliary leaves — carry four distinct colors. Delete the three leaves and restore both loops; four terminal incidences at $v$ must be colored.

Transfer the three leaf colors to three of the four terminal incidences and choose the fourth freely, subject to one constraint: each loop of length exactly 3 must receive distinct colors on its two terminal edges (its middle edge is adjacent to exactly those two edges, and the interior extension requires them distinct). This is always possible: the loop containing the free terminal has its mate already colored, leaving four admissible choices; the other loop's two terminals carry two of the three transferred colors, distinct by construction.

The five incidences at the restored $v$ then carry at least four distinct colors — the four distinct colors of $G_4$ all transfer, and the free terminal either repeats one of them or introduces the fifth — so every color has multiplicity at most $2 = \lfloor (5-1)/2 \rfloor$ and $v$ is balanced at its restored degree 5. Each terminal edge (endpoint degrees 5 and 2, threshold $\lfloor(5+2-2)/2\rfloor = 2$) therefore sees at most 2 same-colored edges on its $v$-side. The loop interiors then extend exactly by the length-at-least-3 argument of Claim 10: each interior edge has at most $2+2 < 5$ forbidden colors, and the greedy order maintains the strong-majority condition of the already-colored terminal edges. Equivalently, one may restore the two loops one at a time in reverse processing order — the two-leaf transfer for the second-processed loop, then the single-leaf step at four distinct colors for the first.

The repair uses Claim 8, the distinctness observation of Remark 9, and Claim 10 — no new machinery — and the statement of Theorem 2 is unaffected.

## Closing

We hope these notes are useful for a revision. Observation 1 seems to need only the sentence already present in Remark 6; observation 2 is the deletion of one paragraph; observation 3 seems to need a short paragraph along the lines of Section 3.4, or any equivalent treatment the authors prefer. We would of course welcome corrections to anything above.
