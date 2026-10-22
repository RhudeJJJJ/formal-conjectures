/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1Norm30UDirect
import Proofs.RadenkovicGutmanD1Norm30UInverse
import Proofs.RadenkovicGutmanD1Norm30VDirect
import Proofs.RadenkovicGutmanD1Norm30VInverse
import Proofs.RadenkovicGutmanD1Norm30JDirect
import Proofs.RadenkovicGutmanD1Norm30JInverse
namespace Gebendorfer.RadenkovicGutman.DegreeOneNormPack30
set_option maxHeartbeats 0
def pack : NormProgramPack.Pack 1 2 4 := {
  u := uDirect
  ui := uInverse
  du := 60
  v := vDirect
  vi := vInverse
  dv := 56
  j := jDirect
  ji := jInverse
  dj := 60
  hu := NormProgramPack.compile_eq_of_accepts _ _ uDirect_checked
  hui := NormProgramPack.compile_eq_of_accepts _ _ uInverse_checked
  hdu := uDegree_checked
  hv := NormProgramPack.compile_eq_of_accepts _ _ vDirect_checked
  hvi := NormProgramPack.compile_eq_of_accepts _ _ vInverse_checked
  hdv := vDegree_checked
  hj := NormProgramPack.compile_eq_of_accepts _ _ jDirect_checked
  hji := NormProgramPack.compile_eq_of_accepts _ _ jInverse_checked
  hdj := jDegree_checked
}
theorem pack_polynomial_checked (reciprocal : Bool) (s L : ℚ) :
    NestedArithmetic.accepts (ComputedClassCell.polynomial 1 2 4 reciprocal s L)
      (NormProgramPack.polynomial pack reciprocal s L)=true :=
  NormProgramPack.accepts_polynomial pack reciprocal s L
#print axioms pack_polynomial_checked
end Gebendorfer.RadenkovicGutman.DegreeOneNormPack30
