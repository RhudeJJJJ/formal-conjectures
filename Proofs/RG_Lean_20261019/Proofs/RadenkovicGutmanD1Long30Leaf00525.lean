/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00525 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 11272903223257844110804280934400000000000 89789148312380412384034064499707215872 114788353451951256854593536000000000000))
theorem leaf00525_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 11272903223257844110804280934400000000000 89789148312380412384034064499707215872 114788353451951256854593536000000000000 raw00525=true := by decide +kernel
#print axioms leaf00525_raw
theorem leaf00525_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00525=true := by decide +kernel
#print axioms leaf00525_rectangular
def affine00525 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00525 (IntegerComputedClassCell.leftNumerator ![(3/200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/200),0,0] ![(1/3200),1,(1/16)]))
theorem leaf00525_transform : affine00525=(NestedInteger.clearedAll 3 raw00525 (IntegerComputedClassCell.leftNumerator ![(3/200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/200),0,0] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00525_transform
theorem leaf00525_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00525=true := by decide +kernel
#print axioms leaf00525_sign
theorem leaf00525_log : RationalLog.accepts (9597495/2147483648) (-5809533873/2147483648) 8 8=true := by decide +kernel
#print axioms leaf00525_log
def leaf00525 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (97776849319/125000000000) (9597495/2147483648) (-5809533873/2147483648) 8 8 ![60,0,4] ![(3/200),0,0] ![(1/3200),1,(1/16)] affine00525
theorem leaf00525_checked : FastNestedCellData.accepts 1 2 4 leaf00525=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (97776849319/125000000000) (9597495/2147483648) (-5809533873/2147483648) 8 8 ![60,0,4] ![(3/200),0,0] ![(1/3200),1,(1/16)] 11272903223257844110804280934400000000000 89789148312380412384034064499707215872 114788353451951256854593536000000000000 raw00525 affine00525
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00525_raw leaf00525_rectangular
    leaf00525_transform leaf00525_sign leaf00525_log
#print axioms leaf00525_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
