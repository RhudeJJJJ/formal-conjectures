/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00110 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 277620822327788013126267437056000000000000 28654533613480063524041369519829024768 118998379626059403286806528000000000000))
theorem leaf00110_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 277620822327788013126267437056000000000000 28654533613480063524041369519829024768 118998379626059403286806528000000000000 raw00110=true := by decide +kernel
#print axioms leaf00110_raw
theorem leaf00110_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00110=true := by decide +kernel
#print axioms leaf00110_rectangular
def affine00110 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00110 (IntegerComputedClassCell.leftNumerator ![(41/16000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(41/16000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(41/16000),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00110_transform : affine00110=(NestedInteger.clearedAll 3 raw00110 (IntegerComputedClassCell.leftNumerator ![(41/16000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(41/16000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(41/16000),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00110_transform
theorem leaf00110_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00110=true := by decide +kernel
#print axioms leaf00110_sign
theorem leaf00110_log : RationalLog.accepts (357273/4294967296) (-20174437493/4294967296) 14 8=true := by decide +kernel
#print axioms leaf00110_log
def leaf00110 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (60199419739/250000000000) (357273/4294967296) (-20174437493/4294967296) 14 8 ![60,0,4] ![(41/16000),0,0] ![(3/32000),1,(1/16)] affine00110
theorem leaf00110_checked : FastNestedCellData.accepts 1 2 4 leaf00110=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (60199419739/250000000000) (357273/4294967296) (-20174437493/4294967296) 14 8 ![60,0,4] ![(41/16000),0,0] ![(3/32000),1,(1/16)] 277620822327788013126267437056000000000000 28654533613480063524041369519829024768 118998379626059403286806528000000000000 raw00110 affine00110
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00110_raw leaf00110_rectangular
    leaf00110_transform leaf00110_sign leaf00110_log
#print axioms leaf00110_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
