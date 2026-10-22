/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00429 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 77732804313419489107979010048000000000000 90751837242152365064332814435516229353472 5384071533927414096776245805056000000000000))
theorem leaf00429_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 77732804313419489107979010048000000000000 90751837242152365064332814435516229353472 5384071533927414096776245805056000000000000 raw00429=true := by decide +kernel
#print axioms leaf00429_raw
theorem leaf00429_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00429=true := by decide +kernel
#print axioms leaf00429_rectangular
def affine00429 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00429 (IntegerComputedClassCell.leftNumerator ![(11/32),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/32),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/32),0,0] ![(1/32),1,(1/2)]))
theorem leaf00429_transform : affine00429=(NestedInteger.clearedAll 3 raw00429 (IntegerComputedClassCell.leftNumerator ![(11/32),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/32),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/32),0,0] ![(1/32),1,(1/2)])) := by decide +kernel
#print axioms leaf00429_transform
theorem leaf00429_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00429=true := by decide +kernel
#print axioms leaf00429_sign
theorem leaf00429_log : RationalLog.accepts (4931189137/4294967296) (148322639/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00429_log
def leaf00429 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (8427807531/500000000000) (4931189137/4294967296) (148322639/2147483648) 0 8 ![52,0,4] ![(11/32),0,0] ![(1/32),1,(1/2)] affine00429
theorem leaf00429_checked : FastNestedCellData.accepts 1 0 4 leaf00429=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (8427807531/500000000000) (4931189137/4294967296) (148322639/2147483648) 0 8 ![52,0,4] ![(11/32),0,0] ![(1/32),1,(1/2)] 77732804313419489107979010048000000000000 90751837242152365064332814435516229353472 5384071533927414096776245805056000000000000 raw00429 affine00429
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00429_raw leaf00429_rectangular
    leaf00429_transform leaf00429_sign leaf00429_log
#print axioms leaf00429_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
