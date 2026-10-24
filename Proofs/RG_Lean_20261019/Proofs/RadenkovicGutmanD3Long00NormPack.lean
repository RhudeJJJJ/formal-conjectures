/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00NormUDirect
import Proofs.RadenkovicGutmanD3Long00NormUInverse
import Proofs.RadenkovicGutmanD3Long00NormVDirect
import Proofs.RadenkovicGutmanD3Long00NormVInverse
import Proofs.RadenkovicGutmanD3Long00NormJDirect
import Proofs.RadenkovicGutmanD3Long00NormJInverse
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00NormPack
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def pack : NormProgramPack.Pack 3 4 4 := {
  u := uDirect
  ui := uInverse
  du := 88
  v := vDirect
  vi := vInverse
  dv := 84
  j := jDirect
  ji := jInverse
  dj := 88
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
#print axioms pack
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00NormPack
