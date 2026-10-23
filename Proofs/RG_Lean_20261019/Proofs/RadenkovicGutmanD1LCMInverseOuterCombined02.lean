/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1LCMInverseOuterJoinData02
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
theorem outerSuffix02_join : outerSuffix02=NestedInteger.add (NestedInteger.scale (1024^source03.length) piece02) outerSuffix03 := by decide +kernel
theorem outerSuffix02_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 outerSuffix02) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 1 1 1024 24 source02)) x := by
  have hlen : segment02.length=12 := by decide +kernel
  calc
    _ = (1024 : ℝ)^source03.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 1 1 1024 24 segment02)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 1 1 1024 (24+segment02.length) source03)) x := by
      rw [outerSuffix02_join,cast_add,eval_add,cast_scale,eval_scale,piece02_identity,outerSuffix03_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 1 1 1024 24 (segment02++source03))) x :=
      (IntegerOuterPieces.eval_append 1 1 1024 24 segment02 source03 x).symm
    _ = _ := by rw [show segment02++source03=source02 from List.take_append_drop 12 source02]
#print axioms outerSuffix02_join
#print axioms outerSuffix02_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
