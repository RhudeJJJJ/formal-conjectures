/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00498 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 357885281774039010902016000000000000 357896197648858493514996366270529536 6149102239555667122227314163712000000000000))
theorem leaf00498_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 357885281774039010902016000000000000 357896197648858493514996366270529536 6149102239555667122227314163712000000000000 raw00498=true := by decide +kernel
#print axioms leaf00498_raw
theorem leaf00498_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00498=true := by decide +kernel
#print axioms leaf00498_rectangular
def affine00498 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00498 (IntegerComputedClassCell.leftNumerator ![(1/256),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/256),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.denominator ![(1/256),0,0] ![(1/512),1,1]))
theorem leaf00498_transform : affine00498=(NestedInteger.clearedAll 3 raw00498 (IntegerComputedClassCell.leftNumerator ![(1/256),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/256),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.denominator ![(1/256),0,0] ![(1/512),1,1])) := by decide +kernel
#print axioms leaf00498_transform
theorem leaf00498_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00498=true := by decide +kernel
#print axioms leaf00498_sign
theorem leaf00498_log : RationalLog.accepts (4295098047/4294967296) (32687/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00498_log
def leaf00498 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (58203/1000000000000) (4295098047/4294967296) (32687/2147483648) 0 8 ![52,0,4] ![(1/256),0,0] ![(1/512),1,1] affine00498
theorem leaf00498_checked : FastNestedCellData.accepts 1 0 4 leaf00498=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (58203/1000000000000) (4295098047/4294967296) (32687/2147483648) 0 8 ![52,0,4] ![(1/256),0,0] ![(1/512),1,1] 357885281774039010902016000000000000 357896197648858493514996366270529536 6149102239555667122227314163712000000000000 raw00498 affine00498
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00498_raw leaf00498_rectangular
    leaf00498_transform leaf00498_sign leaf00498_log
#print axioms leaf00498_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
