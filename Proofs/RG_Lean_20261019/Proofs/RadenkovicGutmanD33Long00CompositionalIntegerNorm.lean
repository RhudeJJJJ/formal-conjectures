/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanClosedIntegerDataElaboration
import Proofs.RadenkovicGutmanIntegerNormProgramPack
import Proofs.RadenkovicGutmanD33Long00CompositionalNormPack
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00CompositionalIntegerNorm
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def u : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerComputedClassCell.integerize 3 1 FixedDegree33Long00CompositionalNormPack.pack.u)
theorem u_cast : NestedInteger.castPoly 3 u=FixedDegree33Long00CompositionalNormPack.pack.u := by decide +kernel
#print axioms u_cast
noncomputable def v : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerComputedClassCell.integerize 3 1 FixedDegree33Long00CompositionalNormPack.pack.v)
theorem v_cast : NestedInteger.castPoly 3 v=FixedDegree33Long00CompositionalNormPack.pack.v := by decide +kernel
#print axioms v_cast
noncomputable def j : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerComputedClassCell.integerize 3 1 FixedDegree33Long00CompositionalNormPack.pack.j)
theorem j_cast : NestedInteger.castPoly 3 j=FixedDegree33Long00CompositionalNormPack.pack.j := by decide +kernel
#print axioms j_cast
noncomputable def ui : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerComputedClassCell.integerize 3 1 FixedDegree33Long00CompositionalNormPack.pack.ui)
theorem ui_cast : NestedInteger.castPoly 3 ui=FixedDegree33Long00CompositionalNormPack.pack.ui := by decide +kernel
#print axioms ui_cast
noncomputable def vi : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerComputedClassCell.integerize 3 1 FixedDegree33Long00CompositionalNormPack.pack.vi)
theorem vi_cast : NestedInteger.castPoly 3 vi=FixedDegree33Long00CompositionalNormPack.pack.vi := by decide +kernel
#print axioms vi_cast
noncomputable def ji : NestedInteger.Poly 3 := rg_closed_integer_data% (IntegerComputedClassCell.integerize 3 1 FixedDegree33Long00CompositionalNormPack.pack.ji)
theorem ji_cast : NestedInteger.castPoly 3 ji=FixedDegree33Long00CompositionalNormPack.pack.ji := by decide +kernel
#print axioms ji_cast
noncomputable def pack : IntegerNormProgramPack.Pack FixedDegree33Long00CompositionalNormPack.pack := {
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
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00CompositionalIntegerNorm
