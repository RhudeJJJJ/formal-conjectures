/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00475 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 104396508208909059785280716800000000000 106154446371351003382167618864663232512 234467121804980902745308397568000000000000))
theorem leaf00475_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 104396508208909059785280716800000000000 106154446371351003382167618864663232512 234467121804980902745308397568000000000000 raw00475=true := by decide +kernel
#print axioms leaf00475_raw
theorem leaf00475_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00475=true := by decide +kernel
#print axioms leaf00475_rectangular
def affine00475 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00475 (IntegerComputedClassCell.leftNumerator ![(3/32),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/32),0,(1/2)] ![(1/128),1,(1/4)]))
theorem leaf00475_transform : affine00475=(NestedInteger.clearedAll 3 raw00475 (IntegerComputedClassCell.leftNumerator ![(3/32),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/32),0,(1/2)] ![(1/128),1,(1/4)])) := by decide +kernel
#print axioms leaf00475_transform
theorem leaf00475_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00475=true := by decide +kernel
#print axioms leaf00475_sign
theorem leaf00475_log : RationalLog.accepts (4365314085/4294967296) (34888451/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00475_log
def leaf00475 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (113186921/250000000000) (4365314085/4294967296) (34888451/4294967296) 0 8 ![52,0,4] ![(3/32),0,(1/2)] ![(1/128),1,(1/4)] affine00475
theorem leaf00475_checked : FastNestedCellData.accepts 1 0 4 leaf00475=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (113186921/250000000000) (4365314085/4294967296) (34888451/4294967296) 0 8 ![52,0,4] ![(3/32),0,(1/2)] ![(1/128),1,(1/4)] 104396508208909059785280716800000000000 106154446371351003382167618864663232512 234467121804980902745308397568000000000000 raw00475 affine00475
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00475_raw leaf00475_rectangular
    leaf00475_transform leaf00475_sign leaf00475_log
#print axioms leaf00475_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
