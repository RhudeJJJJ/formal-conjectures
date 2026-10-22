/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00514 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 240565441357743758100362428416000000000000 213634938985507174164130722610327786094592 4095423081580281867294891573248000000000000))
theorem leaf00514_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 240565441357743758100362428416000000000000 213634938985507174164130722610327786094592 4095423081580281867294891573248000000000000 raw00514=true := by decide +kernel
#print axioms leaf00514_raw
theorem leaf00514_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00514=true := by decide +kernel
#print axioms leaf00514_rectangular
def affine00514 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00514 (IntegerComputedClassCell.leftNumerator ![(9/640),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/640),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/640),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00514_transform : affine00514=(NestedInteger.clearedAll 3 raw00514 (IntegerComputedClassCell.leftNumerator ![(9/640),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/640),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/640),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00514_transform
theorem leaf00514_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00514=true := by decide +kernel
#print axioms leaf00514_sign
theorem leaf00514_log : RationalLog.accepts (1812530569/2147483648) (-364154823/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00514_log
def leaf00514 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (52164314829/1000000000000) (1812530569/2147483648) (-364154823/4294967296) 1 8 ![60,0,4] ![(9/640),0,(1/2)] ![(1/3200),1,(1/2)] affine00514
theorem leaf00514_checked : FastNestedCellData.accepts 1 2 4 leaf00514=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (52164314829/1000000000000) (1812530569/2147483648) (-364154823/4294967296) 1 8 ![60,0,4] ![(9/640),0,(1/2)] ![(1/3200),1,(1/2)] 240565441357743758100362428416000000000000 213634938985507174164130722610327786094592 4095423081580281867294891573248000000000000 raw00514 affine00514
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00514_raw leaf00514_rectangular
    leaf00514_transform leaf00514_sign leaf00514_log
#print axioms leaf00514_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
