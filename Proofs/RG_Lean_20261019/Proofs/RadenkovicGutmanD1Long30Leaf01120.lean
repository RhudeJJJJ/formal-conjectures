/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01120 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 740941145149513488238383202304000000000000 911722523809688743997174929441117729456128 5674645068995374623613494755328000000000000))
theorem leaf01120_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 740941145149513488238383202304000000000000 911722523809688743997174929441117729456128 5674645068995374623613494755328000000000000 raw01120=true := by decide +kernel
#print axioms leaf01120_raw
theorem leaf01120_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01120=true := by decide +kernel
#print axioms leaf01120_rectangular
def affine01120 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01120 (IntegerComputedClassCell.leftNumerator ![(11/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/16),0,0] ![(1/16),1,(1/2)]))
theorem leaf01120_transform : affine01120=(NestedInteger.clearedAll 3 raw01120 (IntegerComputedClassCell.leftNumerator ![(11/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/16),0,0] ![(1/16),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/16),0,0] ![(1/16),1,(1/2)])) := by decide +kernel
#print axioms leaf01120_transform
theorem leaf01120_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01120=true := by decide +kernel
#print axioms leaf01120_sign
theorem leaf01120_log : RationalLog.accepts (2276677811/2147483648) (62728555/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01120_log
def leaf01120 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (160665999851/1000000000000) (2276677811/2147483648) (62728555/2147483648) 0 8 ![60,0,4] ![(11/16),0,0] ![(1/16),1,(1/2)] affine01120
theorem leaf01120_checked : FastNestedCellData.accepts 1 2 4 leaf01120=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (160665999851/1000000000000) (2276677811/2147483648) (62728555/2147483648) 0 8 ![60,0,4] ![(11/16),0,0] ![(1/16),1,(1/2)] 740941145149513488238383202304000000000000 911722523809688743997174929441117729456128 5674645068995374623613494755328000000000000 raw01120 affine01120
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01120_raw leaf01120_rectangular
    leaf01120_transform leaf01120_sign leaf01120_log
#print axioms leaf01120_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
