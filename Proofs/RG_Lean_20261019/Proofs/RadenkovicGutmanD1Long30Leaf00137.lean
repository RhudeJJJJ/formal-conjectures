/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00137 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 55126514696039395762892701696000000000000 49339920427420507188584322692783219408896 1031900086737221269524028850176000000000000))
theorem leaf00137_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 55126514696039395762892701696000000000000 49339920427420507188584322692783219408896 1031900086737221269524028850176000000000000 raw00137=true := by decide +kernel
#print axioms leaf00137_raw
theorem leaf00137_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00137=true := by decide +kernel
#print axioms leaf00137_rectangular
def affine00137 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00137 (IntegerComputedClassCell.leftNumerator ![(97/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(97/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(97/32000),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00137_transform : affine00137=(NestedInteger.clearedAll 3 raw00137 (IntegerComputedClassCell.leftNumerator ![(97/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(97/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(97/32000),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00137_transform
theorem leaf00137_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00137=true := by decide +kernel
#print axioms leaf00137_sign
theorem leaf00137_log : RationalLog.accepts (3668709401/4294967296) (-169226027/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00137_log
def leaf00137 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (11953657399/250000000000) (3668709401/4294967296) (-169226027/2147483648) 1 8 ![60,0,4] ![(97/32000),0,(1/8)] ![(3/32000),1,(1/8)] affine00137
theorem leaf00137_checked : FastNestedCellData.accepts 1 2 4 leaf00137=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (11953657399/250000000000) (3668709401/4294967296) (-169226027/2147483648) 1 8 ![60,0,4] ![(97/32000),0,(1/8)] ![(3/32000),1,(1/8)] 55126514696039395762892701696000000000000 49339920427420507188584322692783219408896 1031900086737221269524028850176000000000000 raw00137 affine00137
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00137_raw leaf00137_rectangular
    leaf00137_transform leaf00137_sign leaf00137_log
#print axioms leaf00137_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
