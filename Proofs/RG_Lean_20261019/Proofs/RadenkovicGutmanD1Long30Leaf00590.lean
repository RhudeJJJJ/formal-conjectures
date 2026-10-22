/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00590 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 610606444529007882994391292313600000000000 8080693832431929648641552284379256979456 9764881612401230344863770214400000000000))
theorem leaf00590_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 610606444529007882994391292313600000000000 8080693832431929648641552284379256979456 9764881612401230344863770214400000000000 raw00590=true := by decide +kernel
#print axioms leaf00590_raw
theorem leaf00590_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00590=true := by decide +kernel
#print axioms leaf00590_rectangular
def affine00590 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00590 (IntegerComputedClassCell.leftNumerator ![(61/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(61/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(61/3200),0,0] ![(1/3200),1,(1/16)]))
theorem leaf00590_transform : affine00590=(NestedInteger.clearedAll 3 raw00590 (IntegerComputedClassCell.leftNumerator ![(61/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(61/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(61/3200),0,0] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00590_transform
theorem leaf00590_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00590=true := by decide +kernel
#print axioms leaf00590_sign
theorem leaf00590_log : RationalLog.accepts (31101659/4294967296) (-10582666681/4294967296) 8 8=true := by decide +kernel
#print axioms leaf00590_log
def leaf00590 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (165505208423/200000000000) (31101659/4294967296) (-10582666681/4294967296) 8 8 ![60,0,4] ![(61/3200),0,0] ![(1/3200),1,(1/16)] affine00590
theorem leaf00590_checked : FastNestedCellData.accepts 1 2 4 leaf00590=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (165505208423/200000000000) (31101659/4294967296) (-10582666681/4294967296) 8 8 ![60,0,4] ![(61/3200),0,0] ![(1/3200),1,(1/16)] 610606444529007882994391292313600000000000 8080693832431929648641552284379256979456 9764881612401230344863770214400000000000 raw00590 affine00590
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00590_raw leaf00590_rectangular
    leaf00590_transform leaf00590_sign leaf00590_log
#print axioms leaf00590_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
