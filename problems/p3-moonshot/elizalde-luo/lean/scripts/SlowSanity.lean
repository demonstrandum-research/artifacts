-- One-time slow sanity check (NOT part of the library build):
-- the full real-definition (Contains/Nonnesting/IsMultisetPerm exactly as defined
-- in ElizaldeLuo.Defs) avoider count at n = 4, evaluated by the interpreter.
-- Run: lake env lean scripts\SlowSanity.lean   (takes several minutes)
--
-- NOTE: kernel `decide` for `(avoiders 3).card = 16` was attempted and is
-- infeasible (kernel term explosion, > 25 GB memory): the generic
-- `Fintype.decidableExistsFintype` instance for `Contains` materializes the
-- function space `Fin 4 → Fin 6` per pattern check. The interpreted checks in
-- ElizaldeLuo/Sanity.lean cover n = 3 (full real definition) and n = 4
-- (cross-checked fast form + one-sided real check) instead.
import ElizaldeLuo.Bijection

namespace ElizaldeLuo

def msetPermsAuxS : ℕ → List ℕ → List (List ℕ)
  | 0, _ => [[]]
  | fuel + 1, l =>
      if l.isEmpty then [[]]
      else l.dedup.flatMap fun v => (msetPermsAuxS fuel (l.erase v)).map (v :: ·)

def msetPermsS (l : List ℕ) : List (List ℕ) := msetPermsAuxS l.length l

-- full real-definition count at n = 4 (two-sided, all 2520 words)
#guard ((msetPermsS (baseWord 4)).filter fun w => decide (IsAvoider 4 w)).length == 58

end ElizaldeLuo
