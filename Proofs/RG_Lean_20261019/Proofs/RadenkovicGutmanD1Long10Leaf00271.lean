/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00271 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 6746722977293976569808800448512000000000000 3538397662045646891568736484727001517654016 9674610373427247487211418943488000000000000))
theorem leaf00271_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 6746722977293976569808800448512000000000000 3538397662045646891568736484727001517654016 9674610373427247487211418943488000000000000 raw00271=true := by decide +kernel
#print axioms leaf00271_raw
theorem leaf00271_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00271=true := by decide +kernel
#print axioms leaf00271_rectangular
def affine00271 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00271 (IntegerComputedClassCell.leftNumerator ![(19/320),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/320),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/320),0,(1/4)] ![(1/640),1,(1/4)]))
theorem leaf00271_transform : affine00271=(NestedInteger.clearedAll 3 raw00271 (IntegerComputedClassCell.leftNumerator ![(19/320),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/320),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/320),0,(1/4)] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00271_transform
theorem leaf00271_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00271=true := by decide +kernel
#print axioms leaf00271_sign
theorem leaf00271_log : RationalLog.accepts (1649321829/4294967296) (-2055313185/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00271_log
def leaf00271 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (365740585457/1000000000000) (1649321829/4294967296) (-2055313185/4294967296) 2 8 ![52,0,4] ![(19/320),0,(1/4)] ![(1/640),1,(1/4)] affine00271
theorem leaf00271_checked : FastNestedCellData.accepts 1 0 4 leaf00271=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (365740585457/1000000000000) (1649321829/4294967296) (-2055313185/4294967296) 2 8 ![52,0,4] ![(19/320),0,(1/4)] ![(1/640),1,(1/4)] 6746722977293976569808800448512000000000000 3538397662045646891568736484727001517654016 9674610373427247487211418943488000000000000 raw00271 affine00271
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00271_raw leaf00271_rectangular
    leaf00271_transform leaf00271_sign leaf00271_log
#print axioms leaf00271_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
