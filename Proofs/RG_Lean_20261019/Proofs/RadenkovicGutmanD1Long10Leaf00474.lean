/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00474 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 104396508208909059785280716800000000000 106154446371351003382167618864663232512 234467121804980902745308397568000000000000))
theorem leaf00474_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 104396508208909059785280716800000000000 106154446371351003382167618864663232512 234467121804980902745308397568000000000000 raw00474=true := by decide +kernel
#print axioms leaf00474_raw
theorem leaf00474_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00474=true := by decide +kernel
#print axioms leaf00474_rectangular
def affine00474 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00474 (IntegerComputedClassCell.leftNumerator ![(3/32),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/32),0,0] ![(1/128),1,(1/2)]))
theorem leaf00474_transform : affine00474=(NestedInteger.clearedAll 3 raw00474 (IntegerComputedClassCell.leftNumerator ![(3/32),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/32),0,0] ![(1/128),1,(1/2)])) := by decide +kernel
#print axioms leaf00474_transform
theorem leaf00474_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00474=true := by decide +kernel
#print axioms leaf00474_sign
theorem leaf00474_log : RationalLog.accepts (4365314085/4294967296) (34888451/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00474_log
def leaf00474 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (113186921/250000000000) (4365314085/4294967296) (34888451/4294967296) 0 8 ![52,0,4] ![(3/32),0,0] ![(1/128),1,(1/2)] affine00474
theorem leaf00474_checked : FastNestedCellData.accepts 1 0 4 leaf00474=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (113186921/250000000000) (4365314085/4294967296) (34888451/4294967296) 0 8 ![52,0,4] ![(3/32),0,0] ![(1/128),1,(1/2)] 104396508208909059785280716800000000000 106154446371351003382167618864663232512 234467121804980902745308397568000000000000 raw00474 affine00474
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00474_raw leaf00474_rectangular
    leaf00474_transform leaf00474_sign leaf00474_log
#print axioms leaf00474_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
