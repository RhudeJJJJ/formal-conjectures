/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1LCMInverseOuterJoinData03
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
theorem outerSuffix03_join : outerSuffix03=NestedInteger.add (NestedInteger.scale (1024^source04.length) piece03) outerSuffix04 := by decide +kernel
theorem outerSuffix03_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 outerSuffix03) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 1 1 1024 36 source03)) x := by
  have hlen : segment03.length=12 := by decide +kernel
  calc
    _ = (1024 : ℝ)^source04.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 1 1 1024 36 segment03)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 1 1 1024 (36+segment03.length) source04)) x := by
      rw [outerSuffix03_join,cast_add,eval_add,cast_scale,eval_scale,piece03_identity,outerSuffix04_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 1 1 1024 36 (segment03++source04))) x :=
      (IntegerOuterPieces.eval_append 1 1 1024 36 segment03 source04 x).symm
    _ = _ := by rw [show segment03++source04=source03 from List.take_append_drop 12 source03]
#print axioms outerSuffix03_join
#print axioms outerSuffix03_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
