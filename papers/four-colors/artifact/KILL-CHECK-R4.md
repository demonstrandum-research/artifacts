# KILL-CHECK — Rung-4 harvest claim language (2026-07-12)

House doctrine: nothing external without a same-day kill-check on the central claim.
This gates ALL claim wording for the rung-4 harvest. TRUST ONLY DISK / verbatim sources.

## Sources (verbatim, pulled from arXiv HTML full text)

- **KKPW** = Kalinowski, Kamyczura, Pilśniak, Woźniak, *Strong majority colorings of
  graphs*, arXiv:2605.23828 — https://arxiv.org/abs/2605.23828 (HTML: /html/2605.23828v1)
- **APS** = Antoniuk et al., *Strong Majority Edge-Coloring*, arXiv:2607.00212 —
  https://arxiv.org/abs/2607.00212 (HTML: /html/2607.00212v1)

Notation (both papers): `Maj'(G)` = strong majority index (edge version); an edge-coloring
where for every edge e and color i, at most half the edges adjacent to e have color i.
`Maj(G)` (no prime) = majority (vertex-of-line-graph) version — do NOT confuse.

### KKPW verbatim
- **Conjecture 14.** "If G is an admissible graph, then Maj'(G) ≤ 4."
- **Theorem 12:** general bound Maj'(G) ≤ 8.
- **Proposition 15.** "If each vertex of a graph G has degree divisible by 3, then Maj'(G) ≤ 4."
- **Theorem 18.** "If G is a graph with minimum degree δ(G) ≥ 7, then Maj'(G) ≤ 4."
- **Proposition 20.** "If G is a bipartite graph with minimum degree δ(G) ≥ 4, then Maj'(G) ≤ 4."
- **Proposition 21.** "If all vertices of a graph G have even degrees, then Maj'(G) ≤ 4.
  Moreover, if G is connected and the size of G satisfies ‖G‖ ≡ 0 mod 3, then Maj'(G) ≤ 3."
  (Proof: Euler-tour periodic 1,2,3,1,2,3,… on 3⌊m/3⌋ edges; color 4 on the ≤2 leftover edges.)
- **Regular-graph remark (verbatim):** "Let G be an r-regular graph. It follows from
  Proposition 18 and Observation 11 that Maj'(G) ≤ 3 when r ≥ 9 and r = 2, respectively.
  Moreover, Maj'(G) ≤ 4 for r ∈ {3,6} by Proposition 15, and **for r ∈ {4,8} by
  Proposition 21**. This bound can be improved for r = 6." (Obs. 22: 6-regular ⟹ ≤3.)

### APS verbatim
- **Theorem 2.** "Every admissible graph G satisfies Maj'(G) ≤ 5." (improves 8 → 5.)
- **Theorem 4.** "Every graph G with no vertices of degree 2 or 4 satisfies Maj'(G) ≤ 4.
  In particular, this holds for every graph with δ(G) ≥ 5, lowering the previously known
  minimum-degree threshold for Maj'(G) ≤ 4 from 7 to 5." (Proof: attach one auxiliary leaf
  at each vertex of degree divisible by 4, apply Hilton–de Werra equitable 4-coloring.)
- Snark subdivisions & pendant-K₁,₄ chains: admissible max-degree-3 graphs with Maj' = 4
  (lower bound 4 is genuine; Δ≤3 does not force ≤3).

### Literature sweep (WebSearch, 2026-07-12)
Only these two papers address the **strong majority index Maj'**. Other "strong edge-coloring"
hits (strong chromatic index, subcubic strong list coloring, etc.) are a DIFFERENT invariant
and irrelevant. No 2025–2026 followup proves Conjecture 14 for maxdeg-4, subcubic, or mixed
degree-{3,4} classes. Both source papers are fresh (May/July 2026); no formalization exists.

## VERDICTS (per claim)

**(a) "4-regular ⟹ Maj'(G) ≤ 4" — KNOWN. DO NOT claim as new.**
Explicitly stated by KKPW: r-regular remark, "Maj'(G) ≤ 4 for … r ∈ {4,8} by Proposition 21,"
i.e. every 4-regular graph is even-degree ⟹ Prop 21 gives ≤4 via a one-paragraph Euler-tour
argument. Our own 4-regular statement is a re-proof of a published result, not a new theorem.

**(b) "degrees ⊆ {3,4} ⟹ Maj'(G) ≤ 4" (modulo our ePot lemma) — NEW *for the mixed case only*.**
Decompose the class:
  - all-3 (cubic): KNOWN twice — KKPW Prop 15 (÷3) AND APS Thm 4 (no deg 2/4).
  - all-4 (4-regular): KNOWN — KKPW Prop 21 (even). [verdict (a)]
  - **mixed (both a degree-3 and a degree-4 vertex present): OPEN in the literature.**
    Prop 15 fails (deg 4 ∤ 3); Prop 21 fails (deg 3 odd); APS Thm 4 fails (deg 4 excluded);
    Thm 18 fails (δ=3<7); Prop 20 needs bipartite. Best published bound for such graphs is
    **APS Theorem 2, Maj' ≤ 5.** So degrees-{3,4} at bound 4 is a genuine 5→4 improvement whose
    novel ground is exactly the graphs mixing degree-3 and degree-4 vertices, delivered by a
    single unified argument that also recovers the two known extremes. Novelty is REAL but
    NARROW — it is the mixed/non-regular Δ≤4,δ≥3 case, NOT cubic and NOT 4-regular.
  Contingent on our ePot crux + algebra lemma closing kernel-clean (still sorried per ATTACK-R4).

**(c) Formalization firsts — NEW (state modestly, not as a math claim).**
Strong majority edge-coloring is a 2026 pen-and-paper concept; no Lean/mathlib formalization
of Maj' or Conjecture 14 exists. A kernel-checked Maj'(G) ≤ 4 for ANY nontrivial class (incl.
the known cubic/4-regular cases) is a formalization first. Per methods doctrine: frame as "first
machine-checked proof," never imply the mathematics was open.

## RECOMMENDED CLAIM WORDING (paste-ready)

- SAFE (theorem headline): "Maj'(G) ≤ 4 for every graph with all degrees in {3,4} — the first
  bound of 4 for the **mixed** degree-{3,4} class (graphs carrying both degree-3 and degree-4
  vertices), where the previously best general bound was 5 (Antoniuk et al., arXiv:2607.00212,
  Thm 2). The pure sub-cases were already known: cubic via KKPW Prop 15 / APS Thm 4, and
  4-regular via KKPW Prop 21."
- SAFE (formalization): "the first machine-checked (Lean/kernel) strong-majority result."
- FORBIDDEN: "first proof that 4-regular graphs satisfy Maj' ≤ 4" (KKPW Prop 21).
- FORBIDDEN: "first proof for cubic graphs" (KKPW Prop 15; APS Thm 4).
- FORBIDDEN: "resolves/advances Conjecture 14 for regular graphs" (both regular sub-cases done).
- FORBIDDEN: any phrasing implying degrees-{3,4} was wholly open — only the mixed slice was.
