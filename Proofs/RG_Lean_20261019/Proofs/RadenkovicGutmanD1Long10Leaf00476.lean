/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00476 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 104396508208909059785280716800000000000 106154446371351003382167618864663232512 234467121804980902745308397568000000000000))
theorem leaf00476_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 104396508208909059785280716800000000000 106154446371351003382167618864663232512 234467121804980902745308397568000000000000 raw00476=true := by decide +kernel
#print axioms leaf00476_raw
theorem leaf00476_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00476=true := by decide +kernel
#print axioms leaf00476_rectangular
def affine00476 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00476 (IntegerComputedClassCell.leftNumerator ![(3/32),0,(3/4)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,(3/4)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/32),0,(3/4)] ![(1/128),1,(1/4)]))
theorem leaf00476_transform : affine00476=(NestedInteger.clearedAll 3 raw00476 (IntegerComputedClassCell.leftNumerator ![(3/32),0,(3/4)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,(3/4)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/32),0,(3/4)] ![(1/128),1,(1/4)])) := by decide +kernel
#print axioms leaf00476_transform
theorem leaf00476_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00476=true := by decide +kernel
#print axioms leaf00476_sign
theorem leaf00476_log : RationalLog.accepts (4365314085/4294967296) (34888451/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00476_log
def leaf00476 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (113186921/250000000000) (4365314085/4294967296) (34888451/4294967296) 0 8 ![52,0,4] ![(3/32),0,(3/4)] ![(1/128),1,(1/4)] affine00476
theorem leaf00476_checked : FastNestedCellData.accepts 1 0 4 leaf00476=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (113186921/250000000000) (4365314085/4294967296) (34888451/4294967296) 0 8 ![52,0,4] ![(3/32),0,(3/4)] ![(1/128),1,(1/4)] 104396508208909059785280716800000000000 106154446371351003382167618864663232512 234467121804980902745308397568000000000000 raw00476 affine00476
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00476_raw leaf00476_rectangular
    leaf00476_transform leaf00476_sign leaf00476_log
#print axioms leaf00476_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
