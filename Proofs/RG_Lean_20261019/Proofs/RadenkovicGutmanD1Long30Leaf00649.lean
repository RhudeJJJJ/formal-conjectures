/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00649 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 100268318250582961291901534208000000000000 82924743624704333936725111658147261448192 953498790615003750250603085824000000000000))
theorem leaf00649_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 100268318250582961291901534208000000000000 82924743624704333936725111658147261448192 953498790615003750250603085824000000000000 raw00649=true := by decide +kernel
#print axioms leaf00649_raw
theorem leaf00649_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00649=true := by decide +kernel
#print axioms leaf00649_rectangular
def affine00649 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00649 (IntegerComputedClassCell.leftNumerator ![(19/800),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/800),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/800),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00649_transform : affine00649=(NestedInteger.clearedAll 3 raw00649 (IntegerComputedClassCell.leftNumerator ![(19/800),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/800),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/800),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00649_transform
theorem leaf00649_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00649=true := by decide +kernel
#print axioms leaf00649_sign
theorem leaf00649_log : RationalLog.accepts (816964447/1073741824) (-36682953/268435456) 1 8=true := by decide +kernel
#print axioms leaf00649_log
def leaf00649 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (86968902783/1000000000000) (816964447/1073741824) (-36682953/268435456) 1 8 ![60,0,4] ![(19/800),0,(1/2)] ![(3/6400),1,(1/2)] affine00649
theorem leaf00649_checked : FastNestedCellData.accepts 1 2 4 leaf00649=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (86968902783/1000000000000) (816964447/1073741824) (-36682953/268435456) 1 8 ![60,0,4] ![(19/800),0,(1/2)] ![(3/6400),1,(1/2)] 100268318250582961291901534208000000000000 82924743624704333936725111658147261448192 953498790615003750250603085824000000000000 raw00649 affine00649
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00649_raw leaf00649_rectangular
    leaf00649_transform leaf00649_sign leaf00649_log
#print axioms leaf00649_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
