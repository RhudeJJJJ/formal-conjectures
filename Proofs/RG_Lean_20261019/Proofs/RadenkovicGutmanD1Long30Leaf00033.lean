/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00033 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 197611585898998456198251937792000000000000 192590742891200376707335198758247329693696 17978055936939759746230631006208000000000000))
theorem leaf00033_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 197611585898998456198251937792000000000000 192590742891200376707335198758247329693696 17978055936939759746230631006208000000000000 raw00033=true := by decide +kernel
#print axioms leaf00033_raw
theorem leaf00033_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00033=true := by decide +kernel
#print axioms leaf00033_rectangular
def affine00033 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00033 (IntegerComputedClassCell.leftNumerator ![(11/8000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/8000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/8000),0,(1/4)] ![(1/16000),1,(1/4)]))
theorem leaf00033_transform : affine00033=(NestedInteger.clearedAll 3 raw00033 (IntegerComputedClassCell.leftNumerator ![(11/8000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/8000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/8000),0,(1/4)] ![(1/16000),1,(1/4)])) := by decide +kernel
#print axioms leaf00033_transform
theorem leaf00033_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00033=true := by decide +kernel
#print axioms leaf00033_sign
theorem leaf00033_log : RationalLog.accepts (4141476579/4294967296) (-39075153/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00033_log
def leaf00033 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (10712545537/1000000000000) (4141476579/4294967296) (-39075153/2147483648) 1 8 ![60,0,4] ![(11/8000),0,(1/4)] ![(1/16000),1,(1/4)] affine00033
theorem leaf00033_checked : FastNestedCellData.accepts 1 2 4 leaf00033=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (10712545537/1000000000000) (4141476579/4294967296) (-39075153/2147483648) 1 8 ![60,0,4] ![(11/8000),0,(1/4)] ![(1/16000),1,(1/4)] 197611585898998456198251937792000000000000 192590742891200376707335198758247329693696 17978055936939759746230631006208000000000000 raw00033 affine00033
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00033_raw leaf00033_rectangular
    leaf00033_transform leaf00033_sign leaf00033_log
#print axioms leaf00033_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
