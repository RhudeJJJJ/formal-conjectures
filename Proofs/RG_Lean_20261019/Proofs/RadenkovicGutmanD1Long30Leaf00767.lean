/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00767 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 327503334945353419502099051315200000000000 137369582872954165779714801829980084895744 309495662289050261999940586700800000000000))
theorem leaf00767_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 327503334945353419502099051315200000000000 137369582872954165779714801829980084895744 309495662289050261999940586700800000000000 raw00767=true := by decide +kernel
#print axioms leaf00767_raw
theorem leaf00767_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00767=true := by decide +kernel
#print axioms leaf00767_rectangular
def affine00767 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00767 (IntegerComputedClassCell.leftNumerator ![(23/640),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(23/640),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(23/640),0,(1/8)] ![(3/3200),1,(1/8)]))
theorem leaf00767_transform : affine00767=(NestedInteger.clearedAll 3 raw00767 (IntegerComputedClassCell.leftNumerator ![(23/640),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(23/640),0,(1/8)] ![(3/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(23/640),0,(1/8)] ![(3/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00767_transform
theorem leaf00767_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00767=true := by decide +kernel
#print axioms leaf00767_sign
theorem leaf00767_log : RationalLog.accepts (1247707259/4294967296) (-1327291245/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00767_log
def leaf00767 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (88769956811/200000000000) (1247707259/4294967296) (-1327291245/2147483648) 2 8 ![60,0,4] ![(23/640),0,(1/8)] ![(3/3200),1,(1/8)] affine00767
theorem leaf00767_checked : FastNestedCellData.accepts 1 2 4 leaf00767=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (88769956811/200000000000) (1247707259/4294967296) (-1327291245/2147483648) 2 8 ![60,0,4] ![(23/640),0,(1/8)] ![(3/3200),1,(1/8)] 327503334945353419502099051315200000000000 137369582872954165779714801829980084895744 309495662289050261999940586700800000000000 raw00767 affine00767
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00767_raw leaf00767_rectangular
    leaf00767_transform leaf00767_sign leaf00767_log
#print axioms leaf00767_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
