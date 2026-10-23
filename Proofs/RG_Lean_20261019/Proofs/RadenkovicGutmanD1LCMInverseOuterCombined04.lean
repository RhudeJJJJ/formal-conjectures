/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1LCMInverseOuterJoinData04
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
theorem outerSuffix04_join : outerSuffix04=NestedInteger.add (NestedInteger.scale (1024^source05.length) piece04) outerSuffix05 := by decide +kernel
theorem outerSuffix04_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 outerSuffix04) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 1 1 1024 48 source04)) x := by
  have hlen : segment04.length=12 := by decide +kernel
  calc
    _ = (1024 : ℝ)^source05.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 1 1 1024 48 segment04)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 1 1 1024 (48+segment04.length) source05)) x := by
      rw [outerSuffix04_join,cast_add,eval_add,cast_scale,eval_scale,piece04_identity,outerSuffix05_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 1 1 1024 48 (segment04++source05))) x :=
      (IntegerOuterPieces.eval_append 1 1 1024 48 segment04 source05 x).symm
    _ = _ := by rw [show segment04++source05=source04 from List.take_append_drop 12 source04]
#print axioms outerSuffix04_join
#print axioms outerSuffix04_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
