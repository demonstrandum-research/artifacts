/-
Erdős #866, Campaign 2, P1 — closing the formally pinned T1 target for h₄.

`Erdos866.T1TargetH4` (Statements.lean) is the Prop "B < 2270 and hFun 4 n ≤ B
for all n ≥ 1", pinned at bridgehead time so the campaign goal itself is
formal. `h4_le_1000` (H4Improved.lean) closes it at B = 1000.
-/
import Erdos866.Statements
import Erdos866.H4Improved

/-- **Campaign-2 P1 closure (T1, h₄ side).** The pinned target Prop holds at
B = 1000: a strict improvement of the standing Lean-verified constant 2270. -/
theorem Erdos866.T1TargetH4_closed_1000 : Erdos866.T1TargetH4 1000 :=
  ⟨by norm_num, h4_le_1000⟩

#print axioms Erdos866.T1TargetH4_closed_1000
