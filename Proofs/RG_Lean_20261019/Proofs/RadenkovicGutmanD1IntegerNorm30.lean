/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerNormProgramPack
import Proofs.RadenkovicGutmanD1Norm30Pack
namespace Gebendorfer.RadenkovicGutman.DegreeOneIntegerNorm30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def u : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.integerize 3 1 DegreeOneNormPack30.pack.u)
theorem u_cast : NestedInteger.castPoly 3 u=DegreeOneNormPack30.pack.u := by decide +kernel
#print axioms u_cast
def v : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.integerize 3 1 DegreeOneNormPack30.pack.v)
theorem v_cast : NestedInteger.castPoly 3 v=DegreeOneNormPack30.pack.v := by decide +kernel
#print axioms v_cast
def j : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.integerize 3 1 DegreeOneNormPack30.pack.j)
theorem j_cast : NestedInteger.castPoly 3 j=DegreeOneNormPack30.pack.j := by decide +kernel
#print axioms j_cast
def ui : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.integerize 3 1 DegreeOneNormPack30.pack.ui)
theorem ui_cast : NestedInteger.castPoly 3 ui=DegreeOneNormPack30.pack.ui := by decide +kernel
#print axioms ui_cast
def vi : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.integerize 3 1 DegreeOneNormPack30.pack.vi)
theorem vi_cast : NestedInteger.castPoly 3 vi=DegreeOneNormPack30.pack.vi := by decide +kernel
#print axioms vi_cast
def ji : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.integerize 3 1 DegreeOneNormPack30.pack.ji)
theorem ji_cast : NestedInteger.castPoly 3 ji=DegreeOneNormPack30.pack.ji := by decide +kernel
#print axioms ji_cast
def pack : IntegerNormProgramPack.Pack DegreeOneNormPack30.pack := {
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
end Gebendorfer.RadenkovicGutman.DegreeOneIntegerNorm30
