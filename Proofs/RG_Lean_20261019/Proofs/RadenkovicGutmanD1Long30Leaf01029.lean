/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01029 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 6358701867692644733701704384512000000000000 4947470483683151520089834892646953120694272 14352728548012889931415390519296000000000000))
theorem leaf01029_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 6358701867692644733701704384512000000000000 4947470483683151520089834892646953120694272 14352728548012889931415390519296000000000000 raw01029=true := by decide +kernel
#print axioms leaf01029_raw
theorem leaf01029_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01029=true := by decide +kernel
#print axioms leaf01029_rectangular
def affine01029 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01029 (IntegerComputedClassCell.leftNumerator ![(1/5),0,(1/2)] ![(3/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/5),0,(1/2)] ![(3/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/5),0,(1/2)] ![(3/320),1,(1/2)]))
theorem leaf01029_transform : affine01029=(NestedInteger.clearedAll 3 raw01029 (IntegerComputedClassCell.leftNumerator ![(1/5),0,(1/2)] ![(3/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/5),0,(1/2)] ![(3/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/5),0,(1/2)] ![(3/320),1,(1/2)])) := by decide +kernel
#print axioms leaf01029_transform
theorem leaf01029_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01029=true := by decide +kernel
#print axioms leaf01029_sign
theorem leaf01029_log : RationalLog.accepts (2485119593/4294967296) (-293734517/1073741824) 1 8=true := by decide +kernel
#print axioms leaf01029_log
def leaf01029 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (344705918957/1000000000000) (2485119593/4294967296) (-293734517/1073741824) 1 8 ![60,0,4] ![(1/5),0,(1/2)] ![(3/320),1,(1/2)] affine01029
theorem leaf01029_checked : FastNestedCellData.accepts 1 2 4 leaf01029=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (344705918957/1000000000000) (2485119593/4294967296) (-293734517/1073741824) 1 8 ![60,0,4] ![(1/5),0,(1/2)] ![(3/320),1,(1/2)] 6358701867692644733701704384512000000000000 4947470483683151520089834892646953120694272 14352728548012889931415390519296000000000000 raw01029 affine01029
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01029_raw leaf01029_rectangular
    leaf01029_transform leaf01029_sign leaf01029_log
#print axioms leaf01029_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
