/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00496 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 559080460621475269836800000000000 559148629081788443794674026545152 1201106333199696782566621184000000000000))
theorem leaf00496_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 559080460621475269836800000000000 559148629081788443794674026545152 1201106333199696782566621184000000000000 raw00496=true := by decide +kernel
#print axioms leaf00496_raw
theorem leaf00496_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00496=true := by decide +kernel
#print axioms leaf00496_rectangular
def affine00496 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00496 (IntegerComputedClassCell.leftNumerator ![(1/128),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/128),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(1/128),0,0] ![(1/256),1,1]))
theorem leaf00496_transform : affine00496=(NestedInteger.clearedAll 3 raw00496 (IntegerComputedClassCell.leftNumerator ![(1/128),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/128),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(1/128),0,0] ![(1/256),1,1])) := by decide +kernel
#print axioms leaf00496_transform
theorem leaf00496_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00496=true := by decide +kernel
#print axioms leaf00496_sign
theorem leaf00496_log : RationalLog.accepts (1073872245/1073741824) (130413/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00496_log
def leaf00496 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (58191/125000000000) (1073872245/1073741824) (130413/2147483648) 0 8 ![52,0,4] ![(1/128),0,0] ![(1/256),1,1] affine00496
theorem leaf00496_checked : FastNestedCellData.accepts 1 0 4 leaf00496=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (58191/125000000000) (1073872245/1073741824) (130413/2147483648) 0 8 ![52,0,4] ![(1/128),0,0] ![(1/256),1,1] 559080460621475269836800000000000 559148629081788443794674026545152 1201106333199696782566621184000000000000 raw00496 affine00496
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00496_raw leaf00496_rectangular
    leaf00496_transform leaf00496_sign leaf00496_log
#print axioms leaf00496_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
