/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00915 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 240618785401495684129736359936000000000000 44869119254315623879104347148963289235456 53747437460828505362162253824000000000000))
theorem leaf00915_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 240618785401495684129736359936000000000000 44869119254315623879104347148963289235456 53747437460828505362162253824000000000000 raw00915=true := by decide +kernel
#print axioms leaf00915_raw
theorem leaf00915_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00915=true := by decide +kernel
#print axioms leaf00915_rectangular
def affine00915 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00915 (IntegerComputedClassCell.leftNumerator ![(3/40),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/40),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/40),0,0] ![(1/320),1,(1/16)]))
theorem leaf00915_transform : affine00915=(NestedInteger.clearedAll 3 raw00915 (IntegerComputedClassCell.leftNumerator ![(3/40),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/40),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/40),0,0] ![(1/320),1,(1/16)])) := by decide +kernel
#print axioms leaf00915_transform
theorem leaf00915_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00915=true := by decide +kernel
#print axioms leaf00915_sign
theorem leaf00915_log : RationalLog.accepts (109125391/1073741824) (-4910022349/4294967296) 4 8=true := by decide +kernel
#print axioms leaf00915_log
def leaf00915 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (417407055797/500000000000) (109125391/1073741824) (-4910022349/4294967296) 4 8 ![60,0,4] ![(3/40),0,0] ![(1/320),1,(1/16)] affine00915
theorem leaf00915_checked : FastNestedCellData.accepts 1 2 4 leaf00915=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (417407055797/500000000000) (109125391/1073741824) (-4910022349/4294967296) 4 8 ![60,0,4] ![(3/40),0,0] ![(1/320),1,(1/16)] 240618785401495684129736359936000000000000 44869119254315623879104347148963289235456 53747437460828505362162253824000000000000 raw00915 affine00915
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00915_raw leaf00915_rectangular
    leaf00915_transform leaf00915_sign leaf00915_log
#print axioms leaf00915_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
