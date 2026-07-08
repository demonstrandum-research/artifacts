# 866 release freeze — 2026-07-08 (SUBMIT.md G7)

Frozen artifact set for the 866 paper release (Draft v5, gates G1–G6
green this session; tag `866-freeze-2026-07-08` on the pathspec commit
containing this directory). The FROZEN release set is the **298 cells**
(h4 range to 64, g5 range to 23); post-freeze ladder cells (h4 65–68,
g5 24–25) are NOT in the certified set and are claimed nowhere.

Gate evidence at freeze (check_gate.py, this session):
- G1 canonical: n_cells=298, n_failed=0, fresh; pinned-manifest cell
  list; multi-run assembly disclosed in the report (`resumed: true`,
  `runs` list) per C6P2 G1-RESUME-PLAN.md.
- G2 archive: 273 VERIFIED + 25 TRIVIAL_M_EQ_N = 298/298, 0 FAIL.
- G3 belt: 4/4 late cells (h4_n62..64, g5_n23), 0 failed.
- G6 kill-check 2026-07-08: 8/8 GREEN (one non-superseding
  plby/lean-proofs delta assessed; record in paper §13).

Copies are verbatim from their live locations at freeze time
(audit logs renamed `.log` -> `.log.txt` only because `*.log` is
gitignored repo-wide). sha256:

```
6135bf892fae0b1ecd6b24ec96cc3e478053d63fb004c490ed258bbe8589930a  auditC4P1.log.txt
ffd8db9e7965b29f51fe52431f6caf4d1b8738b95b519ce0812285f768ed0d8d  auditC4Synth.log.txt
920e95e68ae3a5511caa63a56ebd2732566193c58e2e886e8baa5dfc15d510db  draft-866.md
ff557e83e494cc47110193c7c884929a2c92695774ba8f95ee1cc5a810c75abd  draft-866.pdf
45f0eedccfa5e22636108f633cde6c1c28f139d06446d92be6a09858bfc1400e  sat_archive_manifest.json
c27586cd397e36a85ea16b19208349df72c38014a7588106a11669318c9ab26c  tables-866.md
bc7ed9307d915dcfc388f2ae954e2677230727b16ebb48b81e25f6289585d925  verify_new_cells_c5_report.json
83bbf8ea9e1e8e5ce5552a2f11a1e2fb5a4507e5c3c1aca00d77651894c5b807  verify_report.json
```

Source locations:
- verify_report.json <- lab/data/verify_report.json (G1 canonical)
- sat_archive_manifest.json <- lenses/P5-hygiene/sat_archive/manifest.json
  (sha256 = the G1 pin 45f0eedc…)
- verify_new_cells_c5_report.json <- lenses/C5P2-publication-gate/ (G3)
- draft-866.{md,pdf}, tables-866.md <- lenses/C4P4-publication/paper/
  (Draft v5, PDF 21 pp, pdflatex_c7_1/2.log 0 errors)
- audit logs <- lean/scripts/ (G5: auditC4P1 + auditC4Synth, axioms
  exactly [propext, Classical.choice, Quot.sound], zero sorryAx)
