/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00022 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3283916706547276570167345152000000000000 3131513258667253960104310159863145562112 157059359317608381603756638208000000000000))
theorem leaf00022_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3283916706547276570167345152000000000000 3131513258667253960104310159863145562112 157059359317608381603756638208000000000000 raw00022=true := by decide +kernel
#print axioms leaf00022_raw
theorem leaf00022_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00022=true := by decide +kernel
#print axioms leaf00022_rectangular
def affine00022 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00022 (IntegerComputedClassCell.leftNumerator ![(1/800),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/800),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/800),0,(1/8)] ![(1/16000),1,(1/8)]))
theorem leaf00022_transform : affine00022=(NestedInteger.clearedAll 3 raw00022 (IntegerComputedClassCell.leftNumerator ![(1/800),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/800),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/800),0,(1/8)] ![(1/16000),1,(1/8)])) := by decide +kernel
#print axioms leaf00022_transform
theorem leaf00022_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00022=true := by decide +kernel
#print axioms leaf00022_sign
theorem leaf00022_log : RationalLog.accepts (2007788867/2147483648) (-72222803/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00022_log
def leaf00022 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (9969202957/500000000000) (2007788867/2147483648) (-72222803/2147483648) 1 8 ![60,0,4] ![(1/800),0,(1/8)] ![(1/16000),1,(1/8)] affine00022
theorem leaf00022_checked : FastNestedCellData.accepts 1 2 4 leaf00022=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (9969202957/500000000000) (2007788867/2147483648) (-72222803/2147483648) 1 8 ![60,0,4] ![(1/800),0,(1/8)] ![(1/16000),1,(1/8)] 3283916706547276570167345152000000000000 3131513258667253960104310159863145562112 157059359317608381603756638208000000000000 raw00022 affine00022
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00022_raw leaf00022_rectangular
    leaf00022_transform leaf00022_sign leaf00022_log
#print axioms leaf00022_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
