/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00640 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 82081655669254176906319757312000000000000 1642552233371117249145879022559117180928 1922611673352361366322675712000000000000))
theorem leaf00640_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 82081655669254176906319757312000000000000 1642552233371117249145879022559117180928 1922611673352361366322675712000000000000 raw00640=true := by decide +kernel
#print axioms leaf00640_raw
theorem leaf00640_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00640=true := by decide +kernel
#print axioms leaf00640_rectangular
def affine00640 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00640 (IntegerComputedClassCell.leftNumerator ![(149/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(149/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(149/6400),0,0] ![(3/6400),1,(1/16)]))
theorem leaf00640_transform : affine00640=(NestedInteger.clearedAll 3 raw00640 (IntegerComputedClassCell.leftNumerator ![(149/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(149/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(149/6400),0,0] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00640_transform
theorem leaf00640_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00640=true := by decide +kernel
#print axioms leaf00640_sign
theorem leaf00640_log : RationalLog.accepts (5793687/536870912) (-9725929641/4294967296) 7 8=true := by decide +kernel
#print axioms leaf00640_log
def leaf00640 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (854333850219/1000000000000) (5793687/536870912) (-9725929641/4294967296) 7 8 ![60,0,4] ![(149/6400),0,0] ![(3/6400),1,(1/16)] affine00640
theorem leaf00640_checked : FastNestedCellData.accepts 1 2 4 leaf00640=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (854333850219/1000000000000) (5793687/536870912) (-9725929641/4294967296) 7 8 ![60,0,4] ![(149/6400),0,0] ![(3/6400),1,(1/16)] 82081655669254176906319757312000000000000 1642552233371117249145879022559117180928 1922611673352361366322675712000000000000 raw00640 affine00640
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00640_raw leaf00640_rectangular
    leaf00640_transform leaf00640_sign leaf00640_log
#print axioms leaf00640_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
