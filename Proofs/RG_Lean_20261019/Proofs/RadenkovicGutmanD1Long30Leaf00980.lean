/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00980 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 118695375911747268385536212992000000000000 48790783099035313229450514194321324900352 67702653150545070221854507008000000000000))
theorem leaf00980_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 118695375911747268385536212992000000000000 48790783099035313229450514194321324900352 67702653150545070221854507008000000000000 raw00980=true := by decide +kernel
#print axioms leaf00980_raw
theorem leaf00980_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00980=true := by decide +kernel
#print axioms leaf00980_rectangular
def affine00980 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00980 (IntegerComputedClassCell.leftNumerator ![(1/8),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/8),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/8),0,0] ![(1/160),1,(1/16)]))
theorem leaf00980_transform : affine00980=(NestedInteger.clearedAll 3 raw00980 (IntegerComputedClassCell.leftNumerator ![(1/8),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/8),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/8),0,0] ![(1/160),1,(1/16)])) := by decide +kernel
#print axioms leaf00980_transform
theorem leaf00980_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00980=true := by decide +kernel
#print axioms leaf00980_sign
theorem leaf00980_log : RationalLog.accepts (513024477/2147483648) (-1537306805/2147483648) 3 8=true := by decide +kernel
#print axioms leaf00980_log
def leaf00980 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (360331396397/500000000000) (513024477/2147483648) (-1537306805/2147483648) 3 8 ![60,0,4] ![(1/8),0,0] ![(1/160),1,(1/16)] affine00980
theorem leaf00980_checked : FastNestedCellData.accepts 1 2 4 leaf00980=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (360331396397/500000000000) (513024477/2147483648) (-1537306805/2147483648) 3 8 ![60,0,4] ![(1/8),0,0] ![(1/160),1,(1/16)] 118695375911747268385536212992000000000000 48790783099035313229450514194321324900352 67702653150545070221854507008000000000000 raw00980 affine00980
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00980_raw leaf00980_rectangular
    leaf00980_transform leaf00980_sign leaf00980_log
#print axioms leaf00980_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
