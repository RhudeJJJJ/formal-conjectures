/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01039 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2098766484781622043911831683072000000000000 1696183993014647170315230172658728628649984 4969438357871051029762313027584000000000000))
theorem leaf01039_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2098766484781622043911831683072000000000000 1696183993014647170315230172658728628649984 4969438357871051029762313027584000000000000 raw01039=true := by decide +kernel
#print axioms leaf01039_raw
theorem leaf01039_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01039=true := by decide +kernel
#print axioms leaf01039_rectangular
def affine01039 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01039 (IntegerComputedClassCell.leftNumerator ![(7/32),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/32),0,(1/2)] ![(3/160),1,(1/2)]))
theorem leaf01039_transform : affine01039=(NestedInteger.clearedAll 3 raw01039 (IntegerComputedClassCell.leftNumerator ![(7/32),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,(1/2)] ![(3/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/32),0,(1/2)] ![(3/160),1,(1/2)])) := by decide +kernel
#print axioms leaf01039_transform
theorem leaf01039_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01039=true := by decide +kernel
#print axioms leaf01039_sign
theorem leaf01039_log : RationalLog.accepts (2587827387/4294967296) (-543984753/2147483648) 1 8=true := by decide +kernel
#print axioms leaf01039_log
def leaf01039 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (341323077351/1000000000000) (2587827387/4294967296) (-543984753/2147483648) 1 8 ![60,0,4] ![(7/32),0,(1/2)] ![(3/160),1,(1/2)] affine01039
theorem leaf01039_checked : FastNestedCellData.accepts 1 2 4 leaf01039=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (341323077351/1000000000000) (2587827387/4294967296) (-543984753/2147483648) 1 8 ![60,0,4] ![(7/32),0,(1/2)] ![(3/160),1,(1/2)] 2098766484781622043911831683072000000000000 1696183993014647170315230172658728628649984 4969438357871051029762313027584000000000000 raw01039 affine01039
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01039_raw leaf01039_rectangular
    leaf01039_transform leaf01039_sign leaf01039_log
#print axioms leaf01039_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
