/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00359 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 36827437998454881861844860928000000000000 34203283951256972665478689285240042553344 1070769614688724113920201064448000000000000))
theorem leaf00359_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 36827437998454881861844860928000000000000 34203283951256972665478689285240042553344 1070769614688724113920201064448000000000000 raw00359=true := by decide +kernel
#print axioms leaf00359_raw
theorem leaf00359_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00359=true := by decide +kernel
#print axioms leaf00359_rectangular
def affine00359 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00359 (IntegerComputedClassCell.leftNumerator ![(11/1280),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/1280),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/1280),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00359_transform : affine00359=(NestedInteger.clearedAll 3 raw00359 (IntegerComputedClassCell.leftNumerator ![(11/1280),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/1280),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/1280),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00359_transform
theorem leaf00359_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00359=true := by decide +kernel
#print axioms leaf00359_sign
theorem leaf00359_log : RationalLog.accepts (3865454561/4294967296) (-14141807/268435456) 1 8=true := by decide +kernel
#print axioms leaf00359_log
def leaf00359 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (7985677657/250000000000) (3865454561/4294967296) (-14141807/268435456) 1 8 ![60,0,4] ![(11/1280),0,(1/2)] ![(1/6400),1,(1/2)] affine00359
theorem leaf00359_checked : FastNestedCellData.accepts 1 2 4 leaf00359=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (7985677657/250000000000) (3865454561/4294967296) (-14141807/268435456) 1 8 ![60,0,4] ![(11/1280),0,(1/2)] ![(1/6400),1,(1/2)] 36827437998454881861844860928000000000000 34203283951256972665478689285240042553344 1070769614688724113920201064448000000000000 raw00359 affine00359
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00359_raw leaf00359_rectangular
    leaf00359_transform leaf00359_sign leaf00359_log
#print axioms leaf00359_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
