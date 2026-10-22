/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00183 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 6881386996205958625602882764800000000000 6418971459232586191556909239391722930176 215089493931590639291700609024000000000000))
theorem leaf00183_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 6881386996205958625602882764800000000000 6418971459232586191556909239391722930176 215089493931590639291700609024000000000000 raw00183=true := by decide +kernel
#print axioms leaf00183_raw
theorem leaf00183_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00183=true := by decide +kernel
#print axioms leaf00183_rectangular
def affine00183 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00183 (IntegerComputedClassCell.leftNumerator ![(31/8000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/8000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/8000),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00183_transform : affine00183=(NestedInteger.clearedAll 3 raw00183 (IntegerComputedClassCell.leftNumerator ![(31/8000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/8000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/8000),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00183_transform
theorem leaf00183_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00183=true := by decide +kernel
#print axioms leaf00183_sign
theorem leaf00183_log : RationalLog.accepts (3890256105/4294967296) (-212534235/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00183_log
def leaf00183 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (7460814731/250000000000) (3890256105/4294967296) (-212534235/4294967296) 1 8 ![60,0,4] ![(31/8000),0,(1/4)] ![(3/32000),1,(1/4)] affine00183
theorem leaf00183_checked : FastNestedCellData.accepts 1 2 4 leaf00183=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (7460814731/250000000000) (3890256105/4294967296) (-212534235/4294967296) 1 8 ![60,0,4] ![(31/8000),0,(1/4)] ![(3/32000),1,(1/4)] 6881386996205958625602882764800000000000 6418971459232586191556909239391722930176 215089493931590639291700609024000000000000 raw00183 affine00183
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00183_raw leaf00183_rectangular
    leaf00183_transform leaf00183_sign leaf00183_log
#print axioms leaf00183_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
