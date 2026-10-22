/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00705 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1006695677148574080746475487232000000000000 32237667685006333661273716280772532371456 36920293963800971865759940608000000000000))
theorem leaf00705_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1006695677148574080746475487232000000000000 32237667685006333661273716280772532371456 36920293963800971865759940608000000000000 raw00705=true := by decide +kernel
#print axioms leaf00705_raw
theorem leaf00705_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00705=true := by decide +kernel
#print axioms leaf00705_rectangular
def affine00705 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00705 (IntegerComputedClassCell.leftNumerator ![(47/1600),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(47/1600),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(47/1600),0,0] ![(3/6400),1,(1/16)]))
theorem leaf00705_transform : affine00705=(NestedInteger.clearedAll 3 raw00705 (IntegerComputedClassCell.leftNumerator ![(47/1600),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(47/1600),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(47/1600),0,0] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00705_transform
theorem leaf00705_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00705=true := by decide +kernel
#print axioms leaf00705_sign
theorem leaf00705_log : RationalLog.accepts (18356431/1073741824) (-4368974931/2147483648) 6 8=true := by decide +kernel
#print axioms leaf00705_log
def leaf00705 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (873169312157/1000000000000) (18356431/1073741824) (-4368974931/2147483648) 6 8 ![60,0,4] ![(47/1600),0,0] ![(3/6400),1,(1/16)] affine00705
theorem leaf00705_checked : FastNestedCellData.accepts 1 2 4 leaf00705=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (873169312157/1000000000000) (18356431/1073741824) (-4368974931/2147483648) 6 8 ![60,0,4] ![(47/1600),0,0] ![(3/6400),1,(1/16)] 1006695677148574080746475487232000000000000 32237667685006333661273716280772532371456 36920293963800971865759940608000000000000 raw00705 affine00705
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00705_raw leaf00705_rectangular
    leaf00705_transform leaf00705_sign leaf00705_log
#print axioms leaf00705_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
