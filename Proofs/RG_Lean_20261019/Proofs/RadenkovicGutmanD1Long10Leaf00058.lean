/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00058 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 178591122878965435210263009689600000000000 159224565962682031369394097224180066942976 3289273029042612601922720366592000000000000))
theorem leaf00058_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 178591122878965435210263009689600000000000 159224565962682031369394097224180066942976 3289273029042612601922720366592000000000000 raw00058=true := by decide +kernel
#print axioms leaf00058_raw
theorem leaf00058_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00058=true := by decide +kernel
#print axioms leaf00058_rectangular
def affine00058 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00058 (IntegerComputedClassCell.leftNumerator ![(1/160),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/160),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/160),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00058_transform : affine00058=(NestedInteger.clearedAll 3 raw00058 (IntegerComputedClassCell.leftNumerator ![(1/160),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/160),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/160),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00058_transform
theorem leaf00058_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00058=true := by decide +kernel
#print axioms leaf00058_sign
theorem leaf00058_log : RationalLog.accepts (3652414545/4294967296) (-174005757/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00058_log
def leaf00058 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (48407220853/1000000000000) (3652414545/4294967296) (-174005757/2147483648) 1 8 ![52,0,4] ![(1/160),0,(1/4)] ![(1/3200),1,(1/4)] affine00058
theorem leaf00058_checked : FastNestedCellData.accepts 1 0 4 leaf00058=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (48407220853/1000000000000) (3652414545/4294967296) (-174005757/2147483648) 1 8 ![52,0,4] ![(1/160),0,(1/4)] ![(1/3200),1,(1/4)] 178591122878965435210263009689600000000000 159224565962682031369394097224180066942976 3289273029042612601922720366592000000000000 raw00058 affine00058
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00058_raw leaf00058_rectangular
    leaf00058_transform leaf00058_sign leaf00058_log
#print axioms leaf00058_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
