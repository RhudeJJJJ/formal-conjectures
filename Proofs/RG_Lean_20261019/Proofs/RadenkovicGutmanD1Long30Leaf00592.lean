/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00592 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1274651774767105808320683835392000000000000 710720713254563060785850271165159397392384 2571385252981481838898218795008000000000000))
theorem leaf00592_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1274651774767105808320683835392000000000000 710720713254563060785850271165159397392384 2571385252981481838898218795008000000000000 raw00592=true := by decide +kernel
#print axioms leaf00592_raw
theorem leaf00592_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00592=true := by decide +kernel
#print axioms leaf00592_rectangular
def affine00592 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00592 (IntegerComputedClassCell.leftNumerator ![(61/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(61/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(61/3200),0,(1/8)] ![(1/3200),1,(1/8)]))
theorem leaf00592_transform : affine00592=(NestedInteger.clearedAll 3 raw00592 (IntegerComputedClassCell.leftNumerator ![(61/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(61/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(61/3200),0,(1/8)] ![(1/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00592_transform
theorem leaf00592_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00592=true := by decide +kernel
#print axioms leaf00592_sign
theorem leaf00592_log : RationalLog.accepts (938105827/2147483648) (-444630749/1073741824) 2 8=true := by decide +kernel
#print axioms leaf00592_log
def leaf00592 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (276396044673/1000000000000) (938105827/2147483648) (-444630749/1073741824) 2 8 ![60,0,4] ![(61/3200),0,(1/8)] ![(1/3200),1,(1/8)] affine00592
theorem leaf00592_checked : FastNestedCellData.accepts 1 2 4 leaf00592=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (276396044673/1000000000000) (938105827/2147483648) (-444630749/1073741824) 2 8 ![60,0,4] ![(61/3200),0,(1/8)] ![(1/3200),1,(1/8)] 1274651774767105808320683835392000000000000 710720713254563060785850271165159397392384 2571385252981481838898218795008000000000000 raw00592 affine00592
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00592_raw leaf00592_rectangular
    leaf00592_transform leaf00592_sign leaf00592_log
#print axioms leaf00592_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
