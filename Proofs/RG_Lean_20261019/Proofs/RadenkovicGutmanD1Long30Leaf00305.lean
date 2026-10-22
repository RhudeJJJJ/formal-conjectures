/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00305 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3375764599760506031019904729088000000000000 4787618704876512349888094231908841422848 8720589993906110347515789312000000000000))
theorem leaf00305_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3375764599760506031019904729088000000000000 4787618704876512349888094231908841422848 8720589993906110347515789312000000000000 raw00305=true := by decide +kernel
#print axioms leaf00305_raw
theorem leaf00305_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00305=true := by decide +kernel
#print axioms leaf00305_rectangular
def affine00305 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00305 (IntegerComputedClassCell.leftNumerator ![(9/1280),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/1280),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/1280),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00305_transform : affine00305=(NestedInteger.clearedAll 3 raw00305 (IntegerComputedClassCell.leftNumerator ![(9/1280),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/1280),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/1280),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00305_transform
theorem leaf00305_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00305=true := by decide +kernel
#print axioms leaf00305_sign
theorem leaf00305_log : RationalLog.accepts (3932379/4294967296) (-15023698567/4294967296) 11 8=true := by decide +kernel
#print axioms leaf00305_log
def leaf00305 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (549001696929/1000000000000) (3932379/4294967296) (-15023698567/4294967296) 11 8 ![60,0,4] ![(9/1280),0,0] ![(1/6400),1,(1/16)] affine00305
theorem leaf00305_checked : FastNestedCellData.accepts 1 2 4 leaf00305=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (549001696929/1000000000000) (3932379/4294967296) (-15023698567/4294967296) 11 8 ![60,0,4] ![(9/1280),0,0] ![(1/6400),1,(1/16)] 3375764599760506031019904729088000000000000 4787618704876512349888094231908841422848 8720589993906110347515789312000000000000 raw00305 affine00305
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00305_raw leaf00305_rectangular
    leaf00305_transform leaf00305_sign leaf00305_log
#print axioms leaf00305_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
