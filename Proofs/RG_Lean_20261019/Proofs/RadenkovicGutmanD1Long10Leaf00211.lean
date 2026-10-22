/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00211 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 18169681965018502878887673856000000000000 10954655394853622759450323638060230639616 43444134728802649429556330496000000000000))
theorem leaf00211_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 18169681965018502878887673856000000000000 10954655394853622759450323638060230639616 43444134728802649429556330496000000000000 raw00211=true := by decide +kernel
#print axioms leaf00211_raw
theorem leaf00211_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00211=true := by decide +kernel
#print axioms leaf00211_rectangular
def affine00211 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00211 (IntegerComputedClassCell.leftNumerator ![(23/640),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/640),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/640),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00211_transform : affine00211=(NestedInteger.clearedAll 3 raw00211 (IntegerComputedClassCell.leftNumerator ![(23/640),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/640),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/640),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00211_transform
theorem leaf00211_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00211=true := by decide +kernel
#print axioms leaf00211_sign
theorem leaf00211_log : RationalLog.accepts (258501567/536870912) (-784750607/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00211_log
def leaf00211 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (126077495423/500000000000) (258501567/536870912) (-784750607/2147483648) 2 8 ![52,0,4] ![(23/640),0,(1/4)] ![(3/3200),1,(1/4)] affine00211
theorem leaf00211_checked : FastNestedCellData.accepts 1 0 4 leaf00211=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (126077495423/500000000000) (258501567/536870912) (-784750607/2147483648) 2 8 ![52,0,4] ![(23/640),0,(1/4)] ![(3/3200),1,(1/4)] 18169681965018502878887673856000000000000 10954655394853622759450323638060230639616 43444134728802649429556330496000000000000 raw00211 affine00211
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00211_raw leaf00211_rectangular
    leaf00211_transform leaf00211_sign leaf00211_log
#print axioms leaf00211_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
