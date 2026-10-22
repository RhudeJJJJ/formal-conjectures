/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00685 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 978418828912104303316959232000000000000 27449215093903654791940630102528753664 31586747723868274738331648000000000000))
theorem leaf00685_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 978418828912104303316959232000000000000 27449215093903654791940630102528753664 31586747723868274738331648000000000000 raw00685=true := by decide +kernel
#print axioms leaf00685_raw
theorem leaf00685_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00685=true := by decide +kernel
#print axioms leaf00685_rectangular
def affine00685 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00685 (IntegerComputedClassCell.leftNumerator ![(11/400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/400),0,0] ![(3/6400),1,(1/16)]))
theorem leaf00685_transform : affine00685=(NestedInteger.clearedAll 3 raw00685 (IntegerComputedClassCell.leftNumerator ![(11/400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/400),0,0] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00685_transform
theorem leaf00685_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00685=true := by decide +kernel
#print axioms leaf00685_sign
theorem leaf00685_log : RationalLog.accepts (2014667/134217728) (-1127163033/536870912) 7 8=true := by decide +kernel
#print axioms leaf00685_log
def leaf00685 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (217252622317/250000000000) (2014667/134217728) (-1127163033/536870912) 7 8 ![60,0,4] ![(11/400),0,0] ![(3/6400),1,(1/16)] affine00685
theorem leaf00685_checked : FastNestedCellData.accepts 1 2 4 leaf00685=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (217252622317/250000000000) (2014667/134217728) (-1127163033/536870912) 7 8 ![60,0,4] ![(11/400),0,0] ![(3/6400),1,(1/16)] 978418828912104303316959232000000000000 27449215093903654791940630102528753664 31586747723868274738331648000000000000 raw00685 affine00685
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00685_raw leaf00685_rectangular
    leaf00685_transform leaf00685_sign leaf00685_log
#print axioms leaf00685_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
