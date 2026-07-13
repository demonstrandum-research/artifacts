# RELEASE-PREP RECORD — t ≤ 2 flip across all four release surfaces (2026-07-13)

Lane: RELEASE-PREP (single agent). Basis: `R4_three_four_t2` UNCONDITIONAL at commit
`121821a` (OVERNIGHT-REPORT headline + TRIAGE-W12-15.md CONSUMER-REWIRE addendum).
Binding scope law applied everywhere: NOT the full mixed class (general t open); NOT
"first machine-verified in the field" (our released five-color E5 is prior); the correct
firsts = "first machine-checked strong-majority bound of FOUR" + "first bound-4 theorem
covering any mixed degree-{3,4} graphs" (both TOK-qualified). NOTHING sent, published,
merged, or pushed to production. All staging only.

## 0. Kill-check sweep verdict (all four surfaces): PASS

Sweep run over main.tex, claims.md, ZENODO-DRAFT.md, the three outbox bodies, and the
site article for: "first proof that 4-regular", "first proof for cubic",
"resolves/advances/settles Conjecture", "first infinite", "first machine-verified",
"solves", plus a full audit of every "first ..." occurrence. Result: zero violations;
every remaining hit is a meta-reference (a forbidden-list entry or calibration sentence).
Every priority claim carries "to our knowledge" + scope; the t ≤ 2 theorem is nowhere
called the mixed case (always a slice); the general theorem is everywhere conditional;
the descent lemma is nowhere described as closed at t ≤ 2 (only the THEOREM is closed
there, by bypass); E5 is named as the prior machine-checked strong-majority result on
every surface that claims a formalization first.

## 1. PAPER — papers/rung4-four-colors/main.tex (recompiled: pdflatex ×2, 0 errors, 16 pp) + claims.md

Claim-bearing sentences changed (main.tex):
- Draft-date line: now "Draft of 2026-07-13 (v2; v1 of 2026-07-12 presented the t ≤ 2 case as conditional)."
- ABSTRACT, replaced the conditional framing with: "Two theorems close unconditionally, each verified to the Lean 4 kernel ... axiom footprint exactly [propext, Classical.choice, Quot.sound] and no unproved dependency."
- ABSTRACT, new headline sentence: "every finite simple graph with all degrees in {3,4} and at most two degree-3 vertices satisfies Maj′(G) ≤ 4" + "the first bound-of-four theorem to cover any part of the mixed class ... it does not cover the full mixed class, whose general case remains open."
- ABSTRACT: "the two theorems together are, to our knowledge, the first machine-checked proofs of a strong-majority bound of four (our earlier verification machine-checked the general five-color bound)."
- ABSTRACT: "the general degrees-{3,4} theorem, with arbitrarily many degree-3 vertices, is therefore conditional" + "At t ≤ 2 ... a migration argument replaces the descent lemma entirely."
- §1.2: contributions re-lettered (a) t≤2 unconditional / (b) 4-regular / (c) general-conditional / (d) toolkit; new (a) text incl. "it does not cover the full mixed class ... and it does not touch the KKPW conjecture in general"; (c) now "which, if completed, would give the first bound of 4 for the full mixed class" + "(At t ≤ 2 the migration argument of Section 2.7 bypasses the lemma ... for t ≥ 4 no such bypass is known.)"
- §1.3 calibration rewritten to the new lettering ("(a) is unconditional but covers only the t ≤ 2 slice ...").
- §2: added Theorem 2.2 (thm:t2, "unconditional; kernel-checked") and the paragraph "Theorem thm:t2 is the paper's unconditional headline ... the mixed graphs it covers are exactly those with two degree-3 vertices."
- §2.6 final sentence: dropped "proved on paper for ... at most two degree-3 vertices modulo one reachability statement"; now "verified exhaustively on small graphs but not proved" + pointer to §2.7.
- NEW §2.7 (all claim-bearing): consumer-map fact (assembly needs only the existential placement); poisoned_t2_shape; even-parity case void (canonical_strict_of_ellP_even); odd-parity migration (mig_unpoisons, migration_descent); nonbip_void_t2 + bridge + defect calculus; component lift; "Every declaration named in this paragraph is kernel-checked ... no sorry anywhere in the dependency cone"; "The route is t ≤ 2 specific in two load-bearing places ... the descent lemma remains the open condition for Theorem thm:threefour."
- §3.1: "three headline statements"; added verbatim Lean quotes of `numDeg3` and `R4_three_four_t2` (docstring abbreviated to drop the ambiguous "first unconditional mixed-class statement" parenthetical).
- §3.2: "R4_four_regular and R4_three_four_t2 are the first machine-checked proofs of a strong-majority bound of four" (TOK) + "for R4_three_four_t2 ... on that slice the statement itself is, to our knowledge, new — though we emphasize it is a slice, not the mixed class."
- §3.3: layer is now two files (Pins2 + Pins3, with Pins3's open pins declared outside the new cone); audit block adds the `R4_three_four_t2` triple; NEW paragraph: three-way audit (clean build 8029 jobs exit 0; per-decl #print axioms for the whole migration chain; transitive walker ZERO sorry-sources; independent third-environment double-confirm); "On disk Pins2.lean contains exactly one sorry."
- §3.4: NEW sentence recording mig_unpoisons' two independent prover closes (direct accepted, structured as confirmation).
- §5.1: "carries Pins2.lean's only sorry" (was "the file's only sorry").
- §5.3 REWRITTEN: heading "The t ≤ 2 regime: the theorem is closed, the lemma is not"; claims (i) theorem at t≤2 free of the descent lemma, (ii) "The descent lemma itself ... remains unproved even restricted to t ≤ 2", (iii) ladder status at last audited checkpoint (t≤2 residue = one named pin; general scaffold modulo three), (iv) no open pin touches thm:t2's cone. NAVIGATE narrative removed (superseded).
- §5.5 bullet: "the corner cases behind NAVIGATE never fire" → "its corner cases never fire" (ladder-generic).
- §6 Reproduction: audit now includes `#print axioms R4_three_four_t2`; "exhibits the remaining sorrys exactly at the descent lemma and the general-t pins, outside both unconditional theorems' cones."
- §7: unconditional content = t≤2 theorem + 4-regular re-proof; "the mixed class with t ≥ 4 remains conditional on one lemma"; descent-lemma item now cites named pins + the general-t migration analogue as the other attack; scope-of-verification sentence updated to both kernel theorems.

claims.md changes: header title synced to main.tex; new RE-ANCHOR 2026-07-13 block (binding scope law); NEW rows T1–T6 (theorem, audit evidence commit 121821a / walker zero sorry-sources / r4final double-confirm, novelty scope, migration chain with Pins3 line numbers, mig_unpoisons double-close, Pins3 open-pin census); rows 6/8/9/15/51/53/54/68/70 updated to v2 (53–54 superseded-in-place); gates G1/G2/G4/G5 extended to cover R4_three_four_t2; three NEW prohibited wordings (t≤2-as-mixed-class; first-machine-verified-in-field; descent-lemma-closed-at-t≤2).

## 2. WEBSITE — site repo branch rung4-draft (commits 5756316 + 446f578; NOT merged, NOT pushed to production)

Claim-bearing sentences changed (p/strong-majority/four-colors/index.html):
- meta/og descriptions: now lead with the unconditional t≤2 theorem, TOK-qualified, general case still "one descent lemma from complete".
- Date line: "13 July 2026 (updated; first published 12 July) · 4-regular and two-degree-3-vertex theorems kernel-checked · general mixed case conditional · not externally refereed".
- Lede: two kernel-checked theorems; "to our knowledge the first bound of four to reach into the mixed degree-{3,4} class"; general case remains one lemma out.
- §target ¶1: "closing the descent core would give the first bound of 4 for the whole class" (was "for that class").
- §target ¶3 CORRECTED (pre-existing scope violations): "The cubic and 4-regular re-proofs are therefore the first machine-checked strong-majority edge-coloring results" REMOVED — (i) no cubic theorem exists in the Lean artifact (verified by grep of Pins2.lean; the claim was unsupported), (ii) "first machine-checked strong-majority results" violated the scope law (E5 prior). Now: "apart from this program's own five-color verification, we know of no Lean or mathlib formalization ... The theorems on this page are, to our knowledge, the first machine-checked strong-majority bounds of four."
- CONDITIONAL:DESCENT-STATUS block REPLACED (ALT adapted scope-honestly): R4_three_four_t2 kernel-complete and unconditional; t=2 graphs mixed, TOK-first on the slice, best published bound there was 5; migration bypass named; "The scope is a slice, not the class"; R4_three_four still rests on the open lemma; Conjecture 14 open; 4-regular kernel-complete as a re-proof. (The old block's "Kernel-complete today are ... cubic and 4-regular" cubic claim is gone.)
- §descent-core closing line: "Closing it would finish R4_three_four in general; the at-most-two-degree-3-vertices case no longer waits on it."
- Artifacts shelf: Lean item now "Pins2.lean + Pins3.lean" with per-file roles.
- Editor pass: ASCII-clean verified (0 non-ASCII bytes); all internal link targets exist on disk; external links unchanged (arXiv ×2, mathlib PR, ORCID, GitHub); LINK-PENDING tokens retained for packaging.

## 3. EMAILS — C:\Users\jacks\.demonstrandum\outbox\ (drafts only; send gates in STAGING-NOTE.md)

- body_kkpw_rung4.txt REWRITTEN: 4-regular formalization credited to their Prop 21; the t≤2 theorem as "a statement I believe is new, though only on a thin slice"; explicit "this does not settle the mixed case ... general degree-{3,4} statement remains conditional, and nothing here touches Conjecture 14 itself"; five labeled one-click link slots; obligation released; ONE question (degree-3 clustering vs spread).
- body_aps_rung4.txt REWRITTEN: t≤2 theorem as "a first slice" of the mixed ground their Thm 2 bounds at five; "on that slice the bound improves from five to four"; general case conditional; three link slots; ONE soft question (equitable-coloring route with degree-4 vertices present).
- body_roucairol_update.txt NEW (4 sentences): arXiv moderation declined the 143/154 note; permanent DOI token; "your suggestion ... was incorporated" — MADE TRUE ON DISK: papers/graffiti-143-154/note.tex now carries the "Related outcomes on neighbouring conjectures" paragraph (142 + 269 certified refutations, communicated separately; four apparent hits recovering FMS-1993/BDF-1995 results; one regular-only discard; survivors/ambiguous), backed by problems/p2-graffiti-avgdist/ certified-kill writeups and the owner-approved 2026-07-10 sent email; note.pdf recompiled (pdflatex ×2, 0 errors, 11 pp).
- STAGING-NOTE.md REWRITTEN: full pending-token table at top (PAPER-PDF, ZENODO, LEAN-PINS3, LEAN-PINS2, AUDIT, GRAFFITI-DOI + the four site tokens), per-draft recipient/thread/content records, 8-step send checklist (G1–G5, deposit-by-owner-order, links-review-on-transmission, kill-check G2 re-run, PROFILE-ALWAYS, humanize pass STILL REQUIRED on the 2026-07-13 rewrites, per-item owner approval, same-day logging).

## 4. ZENODO DRAFT — ZENODO-DRAFT.md (draft only; nothing uploaded, nothing reserved)

- Title: "Machine-checked four-color strong-majority theorems in Lean 4: graphs with degrees in {3,4} and at most two degree-3 vertices, and 4-regular graphs".
- Description rewritten: Theorem 1 = R4_three_four_t2 with the slice caveat and no claim on the general case or Conjecture 14; Theorem 2 = R4_four_regular framed as formalization of KKPW Prop 21; audit sentence (triple, zero sorry-carrying constants, walker output shipped).
- Related-identifiers note (binding): the E5 deposit "not this one, is the first machine-checked strong-majority result; this one adds the first machine-checked bound of FOUR".
- Files: Pins3.lean + AuditPins3.lean + walker now REQUIRED (supersedes the 4-regular-only exclusion); READING-KIT.md flagged as needing a t≤2 section before deposit.
- Target commit updated to `121821a` with the gate evidence.

## 5. Open items needing the owner / later lanes

1. G1 fresh clean-environment rebuild — **DISCHARGED 2026-07-13**. See §6 below.
2. READING-KIT.md t≤2 section + BUNDLE-MANIFEST refresh before deposit (named in ZENODO-DRAFT).
3. Humanize pass (Codex) on the three rewritten email bodies — required by the checklist, deliberately left to the send-time lane.
4. Graffiti note: deposit must use the RECOMPILED note.pdf; re-run its checkers per BUILD.md at deposit time; the added paragraph says 142/269 are "communicated separately" (they are: Roucairol email 2026-07-10) — if the owner prefers them IN the deposit, add the two kill bundles then.
5. All LINK-PENDING tokens resolve at packaging; links-review binds at transmission.

## 6. G1 DISCHARGED — clean-environment rebuild + per-decl axiom audit (2026-07-13)

Procedure: the three release sources were extracted from git **HEAD `6c7f364`**
(`git show HEAD:...` for `Maj5Base.lean`, `Pins2.lean`, `Pins3.lean`; Pins3 byte-identical
to kernel-check commit `121821a`, sha256 `5637e6df…`, and the working tree is clean) into
an isolated staging dir, then submitted to the **Modal Lean farm** — a fresh container with
a warm mathlib cache pinned to `rev 8f9d9cff…` / `leanprover/lean4:v4.28.0`, i.e. a clean
environment that compiles only our sources. Target `Pins3`; per-decl `#print axioms` on the
seven release declarations.

Result: Modal call `fc-01KXEC3Z42KZZGRX2J5SD5V5MR`, `ok=true`, `returncode=0`, `wall=523.9s`,
**`Build completed successfully (8029 jobs)`**. Every one of the seven decls printed EXACTLY
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`:

```
'Rung4Moonshot.R4_three_four_t2'                  depends on axioms: [propext, Classical.choice, Quot.sound]
'Rung4Moonshot.R4_three_four_connected_t2'        depends on axioms: [propext, Classical.choice, Quot.sound]
'Rung4Moonshot.R4_four_regular'                   depends on axioms: [propext, Classical.choice, Quot.sound]
'Rung4Moonshot.mig_unpoisons'                     depends on axioms: [propext, Classical.choice, Quot.sound]
'Rung4Moonshot.migration_safe_split_placement_t2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Rung4Moonshot.navchar_of_blocked'                depends on axioms: [propext, Classical.choice, Quot.sound]
'Rung4Moonshot.exists_alternating_euler_trail'    depends on axioms: [propext, Classical.choice, Quot.sound]
```

NOTE / STALE-ARTIFACT RECONCILED: the farm `gate.json` dated 08:55 (in `scripts/modal_farm/`)
shows `mig_unpoisons` and `migration_safe_split_placement_t2` carrying `sorryAx`; that build
predates the 121821a consumer rewire and is superseded by this HEAD build, in which both are
clean. The in-source docstring at `Pins3.lean:8703` ("sole sorry source is `mig_unpoisons`")
is likewise stale narrative (pre-rewire) — not a claim-bearing release surface; Pins3 source
is not edited here.

## 7. PUBLISH — executed 2026-07-13 (owner-authorized full publication; emails NOT sent)

Lane: PUBLISH (single agent). Basis commit: maths HEAD `4a7cb71` (Pins3 byte-identical to
kernel-check `121821a`, sha256 `5637e6df…`; all Lean sources extracted via `git show HEAD:`,
never the working tree). Graffiti checkers re-run pre-deposit: 143 `CHECKER VERDICT: ACCEPT`,
154 `OVERALL: ALL CHECKS PASS`.

### Zenodo deposit 1 — rung-4 four-color theorems (PUBLISHED)

- **Version DOI: `10.5281/zenodo.21344301`** · concept DOI `10.5281/zenodo.21344300`
- Record: <https://zenodo.org/records/21344301>
- Files (12): main.pdf, claims.md, Maj5Base.lean, Pins2.lean, Pins3.lean, AuditPins2.lean,
  AuditPins3.lean, Demos.lean, READING-KIT.md, RELEASE-PREP-RECORD.md (pre-§7 state),
  CONFIRM-R4FOURREG.md, KILL-CHECK-R4.md
- Metadata per ZENODO-DRAFT.md (title, ~230-word kill-check-compliant description, keywords,
  related identifiers incl. the binding E5-priority note). Type Software; license CC-BY-4.0
  (consistent with the five-color record; the owner's Apache-2.0-for-code option was never
  decided — flag if the owner wants a v2 with a split license statement).

### Zenodo deposit 2 — Graffiti 143/154 note + four kill bundles (PUBLISHED)

- **Version DOI: `10.5281/zenodo.21344321`** · concept DOI `10.5281/zenodo.21344320`
- Record: <https://zenodo.org/records/21344321>
- Files (5): note.pdf (recompiled 11 pp) + graffiti-143/154/142/269-bundle.zip per
  SUBMIT.md's verified lists (no `__pycache__`; third-party rc/cocoon/bdf PDFs excluded —
  their URLs are in the bundles' PROVENANCE records; wow-july2004.pdf included per list).
- CORRECTION FOLDED IN: note.tex's Data-availability paragraph cited the stale multi-paper
  v1 DOI `10.5281/zenodo.20673865` while claiming "the archive record accompanying this note
  contains four certificate bundles". The deposit's DOI was pre-reserved, the URL repointed
  to `10.5281/zenodo.21344321`, and the note recompiled (pdflatex ×2, 0 errors, 11 pp)
  BEFORE upload; maths commit `d0781c3`.

### Artifacts repository (PUSHED)

- `demonstrandum-artifacts` main `9b0b0ce` → `832976a`: new `papers/four-colors/` bundle
  (README, main.pdf/tex, claims.md, artifact/{README, READING-KIT, CONFIRM, KILL-CHECK,
  RELEASE-PREP-RECORD}, artifact/lean/{6 Lean files + HASHES.txt}).
- Public byte check: raw Pins3.lean sha256 = `5637e6df…` (exact kernel-check bytes).

### Site (PRODUCTION)

- `rung4-draft` token fill commit `d8e38ab` (4 tokens + removal of the now-false
  "packaging is pending" notes), merged into main `b77f376`, pushed. Live with title
  "Four Colors: a First Theorem in the Mixed Degree-{3,4} Case"; homepage card and
  flagship-page update came along with the merge.

### URL map (token → live URL)

| Token | URL |
|---|---|
| [LINK-PENDING-PAPER-PDF] | https://zenodo.org/records/21344301/files/main.pdf?download=1 |
| [LINK-PENDING-ZENODO] | https://doi.org/10.5281/zenodo.21344301 |
| [LINK-PENDING-LEAN-PINS3] | https://github.com/demonstrandum-research/artifacts/blob/main/papers/four-colors/artifact/lean/Pins3.lean#L10624 |
| [LINK-PENDING-LEAN-PINS2] | https://github.com/demonstrandum-research/artifacts/blob/main/papers/four-colors/artifact/lean/Pins2.lean#L3447 |
| [LINK-PENDING-AUDIT] | https://github.com/demonstrandum-research/artifacts/blob/main/papers/four-colors/artifact/READING-KIT.md |
| [LINK-PENDING-GRAFFITI-DOI] | https://doi.org/10.5281/zenodo.21344321 |
| [LINK-PENDING-ARCHIVE] (site, filled) | https://doi.org/10.5281/zenodo.21344301 |
| [LINK-PENDING-READING-KIT] (site, filled) | https://github.com/demonstrandum-research/artifacts/blob/main/papers/four-colors/artifact/READING-KIT.md |
| [LINK-PENDING-LEAN] (site, filled) | https://github.com/demonstrandum-research/artifacts/tree/main/papers/four-colors/artifact/lean |
| [LINK-PENDING-CENSUS] (site, filled) | https://github.com/demonstrandum-research/artifacts/blob/main/papers/five-colors/census/README.md |

Email bodies NOT edited (tokens remain in the drafts); the send-time lane substitutes from
this table / the outbox STAGING-NOTE.md table (updated in place). `main.tex` carries no
tokens (only the five-color DOI citation) — not edited, not recompiled.

### Verification (cited-artifact gate, run 2026-07-13 from the public internet)

- All four DOIs resolve 200 through doi.org to the correct records
  (21344301/21344300 → rung-4; 21344321/21344320 → graffiti).
- Zenodo file links serve the exact bytes: main.pdf 463,008 B; note.pdf 428,294 B
  (recompiled version, carries the 21344321 DOI in its Data-availability paragraph).
- All 7 GitHub deep links return 200; raw Pins3.lean sha256 matches `5637e6df…`;
  GitHub code view reports the full 10,651 lines with `"large":false`, so the
  `#L10624` / `#L3447` anchors function.
- Site live on production: article 200 with the new title; homepage 200 with the
  four-colors card; flagship page 200. Zero `LINK-PENDING` tokens and zero non-ASCII
  bytes remain in the published article.
