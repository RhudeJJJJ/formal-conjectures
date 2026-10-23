/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1LCMInverseOuterJoinData05
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
theorem outerSuffix05_join : outerSuffix05=NestedInteger.add (NestedInteger.scale (1024^source06.length) piece05) outerSuffix06 := by decide +kernel
theorem outerSuffix05_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 outerSuffix05) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 1 1 1024 60 source05)) x := by
  have hlen : segment05.length=12 := by decide +kernel
  calc
    _ = (1024 : ℝ)^source06.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 1 1 1024 60 segment05)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 1 1 1024 (60+segment05.length) source06)) x := by
      rw [outerSuffix05_join,cast_add,eval_add,cast_scale,eval_scale,piece05_identity,outerSuffix06_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 1 1 1024 60 (segment05++source06))) x :=
      (IntegerOuterPieces.eval_append 1 1 1024 60 segment05 source06 x).symm
    _ = _ := by rw [show segment05++source06=source05 from List.take_append_drop 12 source05]
#print axioms outerSuffix05_join
#print axioms outerSuffix05_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
