/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00375 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 185323041394234397161263464448000000000000 498539992558487949950370448196713316352 775372390290779270499270656000000000000))
theorem leaf00375_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 185323041394234397161263464448000000000000 498539992558487949950370448196713316352 775372390290779270499270656000000000000 raw00375=true := by decide +kernel
#print axioms leaf00375_raw
theorem leaf00375_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00375=true := by decide +kernel
#print axioms leaf00375_rectangular
def affine00375 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00375 (IntegerComputedClassCell.leftNumerator ![(59/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(59/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(59/6400),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00375_transform : affine00375=(NestedInteger.clearedAll 3 raw00375 (IntegerComputedClassCell.leftNumerator ![(59/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(59/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(59/6400),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00375_transform
theorem leaf00375_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00375=true := by decide +kernel
#print axioms leaf00375_sign
theorem leaf00375_log : RationalLog.accepts (3516181/2147483648) (-3443853355/1073741824) 10 8=true := by decide +kernel
#print axioms leaf00375_log
def leaf00375 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (160742115273/250000000000) (3516181/2147483648) (-3443853355/1073741824) 10 8 ![60,0,4] ![(59/6400),0,0] ![(1/6400),1,(1/16)] affine00375
theorem leaf00375_checked : FastNestedCellData.accepts 1 2 4 leaf00375=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (160742115273/250000000000) (3516181/2147483648) (-3443853355/1073741824) 10 8 ![60,0,4] ![(59/6400),0,0] ![(1/6400),1,(1/16)] 185323041394234397161263464448000000000000 498539992558487949950370448196713316352 775372390290779270499270656000000000000 raw00375 affine00375
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00375_raw leaf00375_rectangular
    leaf00375_transform leaf00375_sign leaf00375_log
#print axioms leaf00375_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
