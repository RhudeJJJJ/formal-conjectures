/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00221 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 9871086694297402349648347136000000000000 7435952585849336340472368249850558414848 54281445327185425242676789248000000000000))
theorem leaf00221_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 9871086694297402349648347136000000000000 7435952585849336340472368249850558414848 54281445327185425242676789248000000000000 raw00221=true := by decide +kernel
#print axioms leaf00221_raw
theorem leaf00221_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00221=true := by decide +kernel
#print axioms leaf00221_rectangular
def affine00221 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00221 (IntegerComputedClassCell.leftNumerator ![(31/800),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(31/800),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(31/800),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00221_transform : affine00221=(NestedInteger.clearedAll 3 raw00221 (IntegerComputedClassCell.leftNumerator ![(31/800),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(31/800),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(31/800),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00221_transform
theorem leaf00221_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00221=true := by decide +kernel
#print axioms leaf00221_sign
theorem leaf00221_log : RationalLog.accepts (2845609503/4294967296) (-27626483/134217728) 1 8=true := by decide +kernel
#print axioms leaf00221_log
def leaf00221 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (8561802911/62500000000) (2845609503/4294967296) (-27626483/134217728) 1 8 ![52,0,4] ![(31/800),0,(1/2)] ![(3/3200),1,(1/2)] affine00221
theorem leaf00221_checked : FastNestedCellData.accepts 1 0 4 leaf00221=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (8561802911/62500000000) (2845609503/4294967296) (-27626483/134217728) 1 8 ![52,0,4] ![(31/800),0,(1/2)] ![(3/3200),1,(1/2)] 9871086694297402349648347136000000000000 7435952585849336340472368249850558414848 54281445327185425242676789248000000000000 raw00221 affine00221
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00221_raw leaf00221_rectangular
    leaf00221_transform leaf00221_sign leaf00221_log
#print axioms leaf00221_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
