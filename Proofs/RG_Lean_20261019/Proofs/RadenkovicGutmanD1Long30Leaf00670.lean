/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00670 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 62332983998278284102091145216000000000000 1573010086473945578229815373523933200384 1818416429924745531478769664000000000000))
theorem leaf00670_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 62332983998278284102091145216000000000000 1573010086473945578229815373523933200384 1818416429924745531478769664000000000000 raw00670=true := by decide +kernel
#print axioms leaf00670_raw
theorem leaf00670_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00670=true := by decide +kernel
#print axioms leaf00670_rectangular
def affine00670 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00670 (IntegerComputedClassCell.leftNumerator ![(167/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(167/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(167/6400),0,0] ![(3/6400),1,(1/16)]))
theorem leaf00670_transform : affine00670=(NestedInteger.clearedAll 3 raw00670 (IntegerComputedClassCell.leftNumerator ![(167/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(167/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(167/6400),0,0] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00670_transform
theorem leaf00670_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00670=true := by decide +kernel
#print axioms leaf00670_sign
theorem leaf00670_log : RationalLog.accepts (14528621/1073741824) (-9240159157/4294967296) 7 8=true := by decide +kernel
#print axioms leaf00670_log
def leaf00670 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (216260981339/250000000000) (14528621/1073741824) (-9240159157/4294967296) 7 8 ![60,0,4] ![(167/6400),0,0] ![(3/6400),1,(1/16)] affine00670
theorem leaf00670_checked : FastNestedCellData.accepts 1 2 4 leaf00670=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (216260981339/250000000000) (14528621/1073741824) (-9240159157/4294967296) 7 8 ![60,0,4] ![(167/6400),0,0] ![(3/6400),1,(1/16)] 62332983998278284102091145216000000000000 1573010086473945578229815373523933200384 1818416429924745531478769664000000000000 raw00670 affine00670
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00670_raw leaf00670_rectangular
    leaf00670_transform leaf00670_sign leaf00670_log
#print axioms leaf00670_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
