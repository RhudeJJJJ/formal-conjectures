/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00949 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1270998871867159856685864976384000000000000 838696656471036616045150537296309204811776 3043122798895392299773964845056000000000000))
theorem leaf00949_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1270998871867159856685864976384000000000000 838696656471036616045150537296309204811776 3043122798895392299773964845056000000000000 raw00949=true := by decide +kernel
#print axioms leaf00949_raw
theorem leaf00949_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00949=true := by decide +kernel
#print axioms leaf00949_rectangular
def affine00949 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00949 (IntegerComputedClassCell.leftNumerator ![(3/32),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/32),0,(1/2)] ![(1/320),1,(1/2)]))
theorem leaf00949_transform : affine00949=(NestedInteger.clearedAll 3 raw00949 (IntegerComputedClassCell.leftNumerator ![(3/32),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/32),0,(1/2)] ![(1/320),1,(1/2)])) := by decide +kernel
#print axioms leaf00949_transform
theorem leaf00949_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00949=true := by decide +kernel
#print axioms leaf00949_sign
theorem leaf00949_log : RationalLog.accepts (1110896907/2147483648) (-707734443/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00949_log
def leaf00949 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (275603947621/1000000000000) (1110896907/2147483648) (-707734443/2147483648) 1 8 ![60,0,4] ![(3/32),0,(1/2)] ![(1/320),1,(1/2)] affine00949
theorem leaf00949_checked : FastNestedCellData.accepts 1 2 4 leaf00949=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (275603947621/1000000000000) (1110896907/2147483648) (-707734443/2147483648) 1 8 ![60,0,4] ![(3/32),0,(1/2)] ![(1/320),1,(1/2)] 1270998871867159856685864976384000000000000 838696656471036616045150537296309204811776 3043122798895392299773964845056000000000000 raw00949 affine00949
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00949_raw leaf00949_rectangular
    leaf00949_transform leaf00949_sign leaf00949_log
#print axioms leaf00949_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
