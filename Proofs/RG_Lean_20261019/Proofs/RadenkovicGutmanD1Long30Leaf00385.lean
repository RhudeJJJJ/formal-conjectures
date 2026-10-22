/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00385 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 11781323742746329864776712192000000000000 34225535839399027921354680069632557056 52333036191378634715430912000000000000))
theorem leaf00385_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 11781323742746329864776712192000000000000 34225535839399027921354680069632557056 52333036191378634715430912000000000000 raw00385=true := by decide +kernel
#print axioms leaf00385_raw
theorem leaf00385_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00385=true := by decide +kernel
#print axioms leaf00385_rectangular
def affine00385 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00385 (IntegerComputedClassCell.leftNumerator ![(61/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(61/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(61/6400),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00385_transform : affine00385=(NestedInteger.clearedAll 3 raw00385 (IntegerComputedClassCell.leftNumerator ![(61/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(61/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(61/6400),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00385_transform
theorem leaf00385_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00385=true := by decide +kernel
#print axioms leaf00385_sign
theorem leaf00385_log : RationalLog.accepts (942957/536870912) (-1703086721/536870912) 10 8=true := by decide +kernel
#print axioms leaf00385_log
def leaf00385 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (163498710997/250000000000) (942957/536870912) (-1703086721/536870912) 10 8 ![60,0,4] ![(61/6400),0,0] ![(1/6400),1,(1/16)] affine00385
theorem leaf00385_checked : FastNestedCellData.accepts 1 2 4 leaf00385=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (163498710997/250000000000) (942957/536870912) (-1703086721/536870912) 10 8 ![60,0,4] ![(61/6400),0,0] ![(1/6400),1,(1/16)] 11781323742746329864776712192000000000000 34225535839399027921354680069632557056 52333036191378634715430912000000000000 raw00385 affine00385
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00385_raw leaf00385_rectangular
    leaf00385_transform leaf00385_sign leaf00385_log
#print axioms leaf00385_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
