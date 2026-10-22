/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00387 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 79925049024559170787488038912000000000000 97927984264083351216892053861808616767488 353153611848802157482324525056000000000000))
theorem leaf00387_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 79925049024559170787488038912000000000000 97927984264083351216892053861808616767488 353153611848802157482324525056000000000000 raw00387=true := by decide +kernel
#print axioms leaf00387_raw
theorem leaf00387_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00387=true := by decide +kernel
#print axioms leaf00387_rectangular
def affine00387 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00387 (IntegerComputedClassCell.leftNumerator ![(1/2),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/2),0,0] ![(1/16),1,(1/2)]))
theorem leaf00387_transform : affine00387=(NestedInteger.clearedAll 3 raw00387 (IntegerComputedClassCell.leftNumerator ![(1/2),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/2),0,0] ![(1/16),1,(1/2)])) := by decide +kernel
#print axioms leaf00387_transform
theorem leaf00387_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00387=true := by decide +kernel
#print axioms leaf00387_sign
theorem leaf00387_log : RationalLog.accepts (514994181/536870912) (-11167477/536870912) 1 8=true := by decide +kernel
#print axioms leaf00387_log
def leaf00387 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (277295717723/1000000000000) (514994181/536870912) (-11167477/536870912) 1 8 ![52,0,4] ![(1/2),0,0] ![(1/16),1,(1/2)] affine00387
theorem leaf00387_checked : FastNestedCellData.accepts 1 0 4 leaf00387=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (277295717723/1000000000000) (514994181/536870912) (-11167477/536870912) 1 8 ![52,0,4] ![(1/2),0,0] ![(1/16),1,(1/2)] 79925049024559170787488038912000000000000 97927984264083351216892053861808616767488 353153611848802157482324525056000000000000 raw00387 affine00387
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00387_raw leaf00387_rectangular
    leaf00387_transform leaf00387_sign leaf00387_log
#print axioms leaf00387_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
