/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00580 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 947857275039254477865241018368000000000000 11698431421963130461726814003811701489664 14229329152947825241487310848000000000000))
theorem leaf00580_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 947857275039254477865241018368000000000000 11698431421963130461726814003811701489664 14229329152947825241487310848000000000000 raw00580=true := by decide +kernel
#print axioms leaf00580_raw
theorem leaf00580_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00580=true := by decide +kernel
#print axioms leaf00580_rectangular
def affine00580 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00580 (IntegerComputedClassCell.leftNumerator ![(59/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(59/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(59/3200),0,0] ![(1/3200),1,(1/16)]))
theorem leaf00580_transform : affine00580=(NestedInteger.clearedAll 3 raw00580 (IntegerComputedClassCell.leftNumerator ![(59/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(59/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(59/3200),0,0] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00580_transform
theorem leaf00580_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00580=true := by decide +kernel
#print axioms leaf00580_sign
theorem leaf00580_log : RationalLog.accepts (7272839/1073741824) (-5363080851/2147483648) 8 8=true := by decide +kernel
#print axioms leaf00580_log
def leaf00580 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (822135133443/1000000000000) (7272839/1073741824) (-5363080851/2147483648) 8 8 ![60,0,4] ![(59/3200),0,0] ![(1/3200),1,(1/16)] affine00580
theorem leaf00580_checked : FastNestedCellData.accepts 1 2 4 leaf00580=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (822135133443/1000000000000) (7272839/1073741824) (-5363080851/2147483648) 8 8 ![60,0,4] ![(59/3200),0,0] ![(1/3200),1,(1/16)] 947857275039254477865241018368000000000000 11698431421963130461726814003811701489664 14229329152947825241487310848000000000000 raw00580 affine00580
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00580_raw leaf00580_rectangular
    leaf00580_transform leaf00580_sign leaf00580_log
#print axioms leaf00580_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
