/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00117 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1937387910028453235093458124800000000000 1756496650834503568603107470759528759296 41810992027657733049009622220800000000000))
theorem leaf00117_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1937387910028453235093458124800000000000 1756496650834503568603107470759528759296 41810992027657733049009622220800000000000 raw00117=true := by decide +kernel
#print axioms leaf00117_raw
theorem leaf00117_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00117=true := by decide +kernel
#print axioms leaf00117_rectangular
def affine00117 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00117 (IntegerComputedClassCell.leftNumerator ![(17/6400),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(17/6400),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(17/6400),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00117_transform : affine00117=(NestedInteger.clearedAll 3 raw00117 (IntegerComputedClassCell.leftNumerator ![(17/6400),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(17/6400),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(17/6400),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00117_transform
theorem leaf00117_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00117=true := by decide +kernel
#print axioms leaf00117_sign
theorem leaf00117_log : RationalLog.accepts (3736960841/4294967296) (-298868061/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00117_log
def leaf00117 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (2100520181/50000000000) (3736960841/4294967296) (-298868061/4294967296) 1 8 ![60,0,4] ![(17/6400),0,(1/8)] ![(3/32000),1,(1/8)] affine00117
theorem leaf00117_checked : FastNestedCellData.accepts 1 2 4 leaf00117=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (2100520181/50000000000) (3736960841/4294967296) (-298868061/4294967296) 1 8 ![60,0,4] ![(17/6400),0,(1/8)] ![(3/32000),1,(1/8)] 1937387910028453235093458124800000000000 1756496650834503568603107470759528759296 41810992027657733049009622220800000000000 raw00117 affine00117
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00117_raw leaf00117_rectangular
    leaf00117_transform leaf00117_sign leaf00117_log
#print axioms leaf00117_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
