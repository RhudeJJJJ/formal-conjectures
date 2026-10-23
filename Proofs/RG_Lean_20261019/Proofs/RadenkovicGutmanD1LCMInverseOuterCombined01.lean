/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1LCMInverseOuterJoinData01
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
theorem outerSuffix01_join : outerSuffix01=NestedInteger.add (NestedInteger.scale (1024^source02.length) piece01) outerSuffix02 := by decide +kernel
theorem outerSuffix01_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 outerSuffix01) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 1 1 1024 12 source01)) x := by
  have hlen : segment01.length=12 := by decide +kernel
  calc
    _ = (1024 : ℝ)^source02.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 1 1 1024 12 segment01)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 1 1 1024 (12+segment01.length) source02)) x := by
      rw [outerSuffix01_join,cast_add,eval_add,cast_scale,eval_scale,piece01_identity,outerSuffix02_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 1 1 1024 12 (segment01++source02))) x :=
      (IntegerOuterPieces.eval_append 1 1 1024 12 segment01 source02 x).symm
    _ = _ := by rw [show segment01++source02=source01 from List.take_append_drop 12 source01]
#print axioms outerSuffix01_join
#print axioms outerSuffix01_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
