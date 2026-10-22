/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00204 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 18280787564798013133054541824000000000000 17609999589528415424310570792028257386496 1110616659753815608626411208704000000000000))
theorem leaf00204_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 18280787564798013133054541824000000000000 17609999589528415424310570792028257386496 1110616659753815608626411208704000000000000 raw00204=true := by decide +kernel
#print axioms leaf00204_raw
theorem leaf00204_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00204=true := by decide +kernel
#print axioms leaf00204_rectangular
def affine00204 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00204 (IntegerComputedClassCell.leftNumerator ![(17/4000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/4000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/4000),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00204_transform : affine00204=(NestedInteger.clearedAll 3 raw00204 (IntegerComputedClassCell.leftNumerator ![(17/4000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/4000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/4000),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00204_transform
theorem leaf00204_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00204=true := by decide +kernel
#print axioms leaf00204_sign
theorem leaf00204_log : RationalLog.accepts (2036395533/2147483648) (-114064513/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00204_log
def leaf00204 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (7928027837/500000000000) (2036395533/2147483648) (-114064513/4294967296) 1 8 ![60,0,4] ![(17/4000),0,(1/2)] ![(3/32000),1,(1/2)] affine00204
theorem leaf00204_checked : FastNestedCellData.accepts 1 2 4 leaf00204=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (7928027837/500000000000) (2036395533/2147483648) (-114064513/4294967296) 1 8 ![60,0,4] ![(17/4000),0,(1/2)] ![(3/32000),1,(1/2)] 18280787564798013133054541824000000000000 17609999589528415424310570792028257386496 1110616659753815608626411208704000000000000 raw00204 affine00204
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00204_raw leaf00204_rectangular
    leaf00204_transform leaf00204_sign leaf00204_log
#print axioms leaf00204_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
