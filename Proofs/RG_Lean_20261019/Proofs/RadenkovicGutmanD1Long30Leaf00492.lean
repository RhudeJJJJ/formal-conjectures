/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00492 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 8758019353168149501653811200000000000 5720283176447541983038615402013786112 29415172704070014210775449600000000000))
theorem leaf00492_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 8758019353168149501653811200000000000 5720283176447541983038615402013786112 29415172704070014210775449600000000000 raw00492=true := by decide +kernel
#print axioms leaf00492_raw
theorem leaf00492_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00492=true := by decide +kernel
#print axioms leaf00492_rectangular
def affine00492 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00492 (IntegerComputedClassCell.leftNumerator ![(41/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(41/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(41/3200),0,(1/8)] ![(1/3200),1,(1/8)]))
theorem leaf00492_transform : affine00492=(NestedInteger.clearedAll 3 raw00492 (IntegerComputedClassCell.leftNumerator ![(41/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(41/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(41/3200),0,(1/8)] ![(1/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00492_transform
theorem leaf00492_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00492=true := by decide +kernel
#print axioms leaf00492_sign
theorem leaf00492_log : RationalLog.accepts (1174268209/2147483648) (-162041499/536870912) 1 8=true := by decide +kernel
#print axioms leaf00492_log
def leaf00492 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (607709671/3125000000) (1174268209/2147483648) (-162041499/536870912) 1 8 ![60,0,4] ![(41/3200),0,(1/8)] ![(1/3200),1,(1/8)] affine00492
theorem leaf00492_checked : FastNestedCellData.accepts 1 2 4 leaf00492=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (607709671/3125000000) (1174268209/2147483648) (-162041499/536870912) 1 8 ![60,0,4] ![(41/3200),0,(1/8)] ![(1/3200),1,(1/8)] 8758019353168149501653811200000000000 5720283176447541983038615402013786112 29415172704070014210775449600000000000 raw00492 affine00492
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00492_raw leaf00492_rectangular
    leaf00492_transform leaf00492_sign leaf00492_log
#print axioms leaf00492_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
