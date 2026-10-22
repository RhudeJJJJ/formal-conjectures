/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00413 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 22618164458117116616949891072000000000000 18959931876602446390132074831248395075584 241612368975536265569782202368000000000000))
theorem leaf00413_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 22618164458117116616949891072000000000000 18959931876602446390132074831248395075584 241612368975536265569782202368000000000000 raw00413=true := by decide +kernel
#print axioms leaf00413_raw
theorem leaf00413_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00413=true := by decide +kernel
#print axioms leaf00413_rectangular
def affine00413 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00413 (IntegerComputedClassCell.leftNumerator ![(33/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(33/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(33/3200),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00413_transform : affine00413=(NestedInteger.clearedAll 3 raw00413 (IntegerComputedClassCell.leftNumerator ![(33/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(33/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(33/3200),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00413_transform
theorem leaf00413_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00413=true := by decide +kernel
#print axioms leaf00413_sign
theorem leaf00413_log : RationalLog.accepts (834584281/1073741824) (-541103907/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00413_log
def leaf00413 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (39236260869/500000000000) (834584281/1073741824) (-541103907/4294967296) 1 8 ![60,0,4] ![(33/3200),0,(1/4)] ![(1/6400),1,(1/4)] affine00413
theorem leaf00413_checked : FastNestedCellData.accepts 1 2 4 leaf00413=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (39236260869/500000000000) (834584281/1073741824) (-541103907/4294967296) 1 8 ![60,0,4] ![(33/3200),0,(1/4)] ![(1/6400),1,(1/4)] 22618164458117116616949891072000000000000 18959931876602446390132074831248395075584 241612368975536265569782202368000000000000 raw00413 affine00413
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00413_raw leaf00413_rectangular
    leaf00413_transform leaf00413_sign leaf00413_log
#print axioms leaf00413_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
