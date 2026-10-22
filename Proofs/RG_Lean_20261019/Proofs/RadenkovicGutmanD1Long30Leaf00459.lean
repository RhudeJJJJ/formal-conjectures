/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00459 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 49997044131291606919038369792000000000000 45293817096536465515019297571292330328064 1044466061217469644791603003392000000000000))
theorem leaf00459_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 49997044131291606919038369792000000000000 45293817096536465515019297571292330328064 1044466061217469644791603003392000000000000 raw00459=true := by decide +kernel
#print axioms leaf00459_raw
theorem leaf00459_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00459=true := by decide +kernel
#print axioms leaf00459_rectangular
def affine00459 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00459 (IntegerComputedClassCell.leftNumerator ![(3/256),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/256),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/256),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00459_transform : affine00459=(NestedInteger.clearedAll 3 raw00459 (IntegerComputedClassCell.leftNumerator ![(3/256),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/256),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/256),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00459_transform
theorem leaf00459_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00459=true := by decide +kernel
#print axioms leaf00459_sign
theorem leaf00459_log : RationalLog.accepts (3729219721/4294967296) (-151660595/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00459_log
def leaf00459 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (10841380773/250000000000) (3729219721/4294967296) (-151660595/2147483648) 1 8 ![60,0,4] ![(3/256),0,(1/2)] ![(1/6400),1,(1/2)] affine00459
theorem leaf00459_checked : FastNestedCellData.accepts 1 2 4 leaf00459=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (10841380773/250000000000) (3729219721/4294967296) (-151660595/2147483648) 1 8 ![60,0,4] ![(3/256),0,(1/2)] ![(1/6400),1,(1/2)] 49997044131291606919038369792000000000000 45293817096536465515019297571292330328064 1044466061217469644791603003392000000000000 raw00459 affine00459
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00459_raw leaf00459_rectangular
    leaf00459_transform leaf00459_sign leaf00459_log
#print axioms leaf00459_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
