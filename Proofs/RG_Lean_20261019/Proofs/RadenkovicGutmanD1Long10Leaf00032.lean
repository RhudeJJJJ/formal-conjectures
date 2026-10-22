/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00032 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 13883358458868285599878479872000000000000 13453030134933813422168452321424198074368 1117185570814216430212500946944000000000000))
theorem leaf00032_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 13883358458868285599878479872000000000000 13453030134933813422168452321424198074368 1117185570814216430212500946944000000000000 raw00032=true := by decide +kernel
#print axioms leaf00032_raw
theorem leaf00032_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00032=true := by decide +kernel
#print axioms leaf00032_rectangular
def affine00032 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00032 (IntegerComputedClassCell.leftNumerator ![(1/320),0,(1/2)] ![(3/8000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/320),0,(1/2)] ![(3/8000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/320),0,(1/2)] ![(3/8000),1,(1/2)]))
theorem leaf00032_transform : affine00032=(NestedInteger.clearedAll 3 raw00032 (IntegerComputedClassCell.leftNumerator ![(1/320),0,(1/2)] ![(3/8000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/320),0,(1/2)] ![(3/8000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/320),0,(1/2)] ![(3/8000),1,(1/2)])) := by decide +kernel
#print axioms leaf00032_transform
theorem leaf00032_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00032=true := by decide +kernel
#print axioms leaf00032_sign
theorem leaf00032_log : RationalLog.accepts (2056160221/2147483648) (-93322133/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00032_log
def leaf00032 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (6020946961/500000000000) (2056160221/2147483648) (-93322133/4294967296) 1 8 ![52,0,4] ![(1/320),0,(1/2)] ![(3/8000),1,(1/2)] affine00032
theorem leaf00032_checked : FastNestedCellData.accepts 1 0 4 leaf00032=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (6020946961/500000000000) (2056160221/2147483648) (-93322133/4294967296) 1 8 ![52,0,4] ![(1/320),0,(1/2)] ![(3/8000),1,(1/2)] 13883358458868285599878479872000000000000 13453030134933813422168452321424198074368 1117185570814216430212500946944000000000000 raw00032 affine00032
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00032_raw leaf00032_rectangular
    leaf00032_transform leaf00032_sign leaf00032_log
#print axioms leaf00032_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
