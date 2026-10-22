/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01053 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1679677165396219376416325632000000000000 1509033938619039740057226475334734446592 4046066008196884402983141376000000000000))
theorem leaf01053_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1679677165396219376416325632000000000000 1509033938619039740057226475334734446592 4046066008196884402983141376000000000000 raw01053=true := by decide +kernel
#print axioms leaf01053_raw
theorem leaf01053_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01053=true := by decide +kernel
#print axioms leaf01053_rectangular
def affine01053 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01053 (IntegerComputedClassCell.leftNumerator ![(11/40),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/40),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/40),0,(1/4)] ![(3/160),1,(1/4)]))
theorem leaf01053_transform : affine01053=(NestedInteger.clearedAll 3 raw01053 (IntegerComputedClassCell.leftNumerator ![(11/40),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/40),0,(1/4)] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/40),0,(1/4)] ![(3/160),1,(1/4)])) := by decide +kernel
#print axioms leaf01053_transform
theorem leaf01053_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01053=true := by decide +kernel
#print axioms leaf01053_sign
theorem leaf01053_log : RationalLog.accepts (702609707/1073741824) (-910754945/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01053_log
def leaf01053 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (23310203287/62500000000) (702609707/1073741824) (-910754945/4294967296) 1 8 ![60,0,4] ![(11/40),0,(1/4)] ![(3/160),1,(1/4)] affine01053
theorem leaf01053_checked : FastNestedCellData.accepts 1 2 4 leaf01053=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (23310203287/62500000000) (702609707/1073741824) (-910754945/4294967296) 1 8 ![60,0,4] ![(11/40),0,(1/4)] ![(3/160),1,(1/4)] 1679677165396219376416325632000000000000 1509033938619039740057226475334734446592 4046066008196884402983141376000000000000 raw01053 affine01053
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01053_raw leaf01053_rectangular
    leaf01053_transform leaf01053_sign leaf01053_log
#print axioms leaf01053_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
