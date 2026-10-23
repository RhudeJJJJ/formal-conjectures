/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1LCMInverseOuterJoinData00
namespace Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
theorem affine01753_join : affine01753=NestedInteger.add (NestedInteger.scale (1024^source01.length) piece00) outerSuffix01 := by decide +kernel
theorem affine01753_eval (x : Fin 3 → ℝ) :
    eval (castPoly 3 affine01753) x=
      eval (castPoly 3 (IntegerOuterTerms.transform 1 1 1024 0 source00)) x := by
  have hlen : segment00.length=12 := by decide +kernel
  calc
    _ = (1024 : ℝ)^source01.length *
        eval (castPoly 3 (IntegerOuterTerms.transform 1 1 1024 0 segment00)) x+
        eval (castPoly 3 (IntegerOuterTerms.transform 1 1 1024 (0+segment00.length) source01)) x := by
      rw [affine01753_join,cast_add,eval_add,cast_scale,eval_scale,piece00_identity,outerSuffix01_eval]
      push_cast
      rw [hlen]
    _ = eval (castPoly 3 (IntegerOuterTerms.transform 1 1 1024 0 (segment00++source01))) x :=
      (IntegerOuterPieces.eval_append 1 1 1024 0 segment00 source01 x).symm
    _ = _ := by rw [show segment00++source01=source00 from List.take_append_drop 12 source00]
#print axioms affine01753_join
#print axioms affine01753_eval
end Gebendorfer.RadenkovicGutman.DegreeOneLCMInversePieces
