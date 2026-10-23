/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1LCMInverseOuterJoinData06
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
theorem outerSuffix06_join : outerSuffix06=NestedInteger.add (NestedInteger.scale (1024^source07.length) piece06) outerSuffix07 := by decide +kernel
theorem outerSuffix06_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 outerSuffix06) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 1 1 1024 72 source06)) x := by
  have hlen : segment06.length=12 := by decide +kernel
  calc
    _ = (1024 : ℝ)^source07.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 1 1 1024 72 segment06)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 1 1 1024 (72+segment06.length) source07)) x := by
      rw [outerSuffix06_join,cast_add,eval_add,cast_scale,eval_scale,piece06_identity,outerSuffix07_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 1 1 1024 72 (segment06++source07))) x :=
      (IntegerOuterPieces.eval_append 1 1 1024 72 segment06 source07 x).symm
    _ = _ := by rw [show segment06++source07=source06 from List.take_append_drop 12 source06]
#print axioms outerSuffix06_join
#print axioms outerSuffix06_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
