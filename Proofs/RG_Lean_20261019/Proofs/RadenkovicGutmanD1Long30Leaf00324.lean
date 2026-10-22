/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00324 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 32200717016610449208928894976000000000000 30172937361098094627062912449395359219712 1080318438959628991608454643712000000000000))
theorem leaf00324_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 32200717016610449208928894976000000000000 30172937361098094627062912449395359219712 1080318438959628991608454643712000000000000 raw00324=true := by decide +kernel
#print axioms leaf00324_raw
theorem leaf00324_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00324=true := by decide +kernel
#print axioms leaf00324_rectangular
def affine00324 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00324 (IntegerComputedClassCell.leftNumerator ![(3/400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/400),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00324_transform : affine00324=(NestedInteger.clearedAll 3 raw00324 (IntegerComputedClassCell.leftNumerator ![(3/400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/400),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00324_transform
theorem leaf00324_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00324=true := by decide +kernel
#print axioms leaf00324_sign
theorem leaf00324_log : RationalLog.accepts (3915150927/4294967296) (-198835679/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00324_log
def leaf00324 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (6982417469/250000000000) (3915150927/4294967296) (-198835679/4294967296) 1 8 ![60,0,4] ![(3/400),0,(1/2)] ![(1/6400),1,(1/2)] affine00324
theorem leaf00324_checked : FastNestedCellData.accepts 1 2 4 leaf00324=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (6982417469/250000000000) (3915150927/4294967296) (-198835679/4294967296) 1 8 ![60,0,4] ![(3/400),0,(1/2)] ![(1/6400),1,(1/2)] 32200717016610449208928894976000000000000 30172937361098094627062912449395359219712 1080318438959628991608454643712000000000000 raw00324 affine00324
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00324_raw leaf00324_rectangular
    leaf00324_transform leaf00324_sign leaf00324_log
#print axioms leaf00324_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
