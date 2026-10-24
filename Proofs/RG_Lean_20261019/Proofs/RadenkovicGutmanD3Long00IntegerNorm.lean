/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanClosedIntegerDataElaboration
import Proofs.RadenkovicGutmanIntegerNormProgramPack
import Proofs.RadenkovicGutmanD3Long00NormPack
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00IntegerNorm
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def u : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerComputedClassCell.integerize 3 1 FixedDegree03Long00NormPack.pack.u)
theorem u_cast : NestedInteger.castPoly 3 u=FixedDegree03Long00NormPack.pack.u := by decide +kernel
#print axioms u_cast
noncomputable def v : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerComputedClassCell.integerize 3 1 FixedDegree03Long00NormPack.pack.v)
theorem v_cast : NestedInteger.castPoly 3 v=FixedDegree03Long00NormPack.pack.v := by decide +kernel
#print axioms v_cast
noncomputable def j : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerComputedClassCell.integerize 3 1 FixedDegree03Long00NormPack.pack.j)
theorem j_cast : NestedInteger.castPoly 3 j=FixedDegree03Long00NormPack.pack.j := by decide +kernel
#print axioms j_cast
noncomputable def ui : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerComputedClassCell.integerize 3 1 FixedDegree03Long00NormPack.pack.ui)
theorem ui_cast : NestedInteger.castPoly 3 ui=FixedDegree03Long00NormPack.pack.ui := by decide +kernel
#print axioms ui_cast
noncomputable def vi : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerComputedClassCell.integerize 3 1 FixedDegree03Long00NormPack.pack.vi)
theorem vi_cast : NestedInteger.castPoly 3 vi=FixedDegree03Long00NormPack.pack.vi := by decide +kernel
#print axioms vi_cast
noncomputable def ji : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerComputedClassCell.integerize 3 1 FixedDegree03Long00NormPack.pack.ji)
theorem ji_cast : NestedInteger.castPoly 3 ji=FixedDegree03Long00NormPack.pack.ji := by decide +kernel
#print axioms ji_cast
noncomputable def pack : IntegerNormProgramPack.Pack FixedDegree03Long00NormPack.pack := {
  u := u
  hu := u_cast
  v := v
  hv := v_cast
  j := j
  hj := j_cast
  ui := ui
  hui := ui_cast
  vi := vi
  hvi := vi_cast
  ji := ji
  hji := ji_cast
}
#print axioms pack
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00IntegerNorm
