/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01180 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 535827564989342081242628096000000000000 650785710661582914900555674763871125504 21879264715258499983176892416000000000000))
theorem leaf01180_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 535827564989342081242628096000000000000 650785710661582914900555674763871125504 21879264715258499983176892416000000000000 raw01180=true := by decide +kernel
#print axioms leaf01180_raw
theorem leaf01180_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01180=true := by decide +kernel
#print axioms leaf01180_rectangular
def affine01180 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01180 (IntegerComputedClassCell.leftNumerator ![(15/32),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(15/32),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.denominator ![(15/32),0,0] ![(1/32),1,(1/2)]))
theorem leaf01180_transform : affine01180=(NestedInteger.clearedAll 3 raw01180 (IntegerComputedClassCell.leftNumerator ![(15/32),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(15/32),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.denominator ![(15/32),0,0] ![(1/32),1,(1/2)])) := by decide +kernel
#print axioms leaf01180_transform
theorem leaf01180_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01180=true := by decide +kernel
#print axioms leaf01180_sign
theorem leaf01180_log : RationalLog.accepts (316609101/268435456) (354458057/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01180_log
def leaf01180 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (14872202497/500000000000) (316609101/268435456) (354458057/4294967296) 0 8 ![60,0,4] ![(15/32),0,0] ![(1/32),1,(1/2)] affine01180
theorem leaf01180_checked : FastNestedCellData.accepts 1 2 4 leaf01180=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (14872202497/500000000000) (316609101/268435456) (354458057/4294967296) 0 8 ![60,0,4] ![(15/32),0,0] ![(1/32),1,(1/2)] 535827564989342081242628096000000000000 650785710661582914900555674763871125504 21879264715258499983176892416000000000000 raw01180 affine01180
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01180_raw leaf01180_rectangular
    leaf01180_transform leaf01180_sign leaf01180_log
#print axioms leaf01180_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
