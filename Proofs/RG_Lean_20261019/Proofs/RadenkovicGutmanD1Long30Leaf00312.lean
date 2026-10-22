/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00312 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 8052819190539258186187145216000000000000 6262187500291370859136275952942995996672 56034806445860993150497062912000000000000))
theorem leaf00312_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 8052819190539258186187145216000000000000 6262187500291370859136275952942995996672 56034806445860993150497062912000000000000 raw00312=true := by decide +kernel
#print axioms leaf00312_raw
theorem leaf00312_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00312=true := by decide +kernel
#print axioms leaf00312_rectangular
def affine00312 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00312 (IntegerComputedClassCell.leftNumerator ![(23/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(23/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(23/3200),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00312_transform : affine00312=(NestedInteger.clearedAll 3 raw00312 (IntegerComputedClassCell.leftNumerator ![(23/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(23/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(23/3200),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00312_transform
theorem leaf00312_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00312=true := by decide +kernel
#print axioms leaf00312_sign
theorem leaf00312_log : RationalLog.accepts (187762467/268435456) (-95947643/536870912) 1 8=true := by decide +kernel
#print axioms leaf00312_log
def leaf00312 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (111755315981/1000000000000) (187762467/268435456) (-95947643/536870912) 1 8 ![60,0,4] ![(23/3200),0,(1/8)] ![(1/6400),1,(1/8)] affine00312
theorem leaf00312_checked : FastNestedCellData.accepts 1 2 4 leaf00312=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (111755315981/1000000000000) (187762467/268435456) (-95947643/536870912) 1 8 ![60,0,4] ![(23/3200),0,(1/8)] ![(1/6400),1,(1/8)] 8052819190539258186187145216000000000000 6262187500291370859136275952942995996672 56034806445860993150497062912000000000000 raw00312 affine00312
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00312_raw leaf00312_rectangular
    leaf00312_transform leaf00312_sign leaf00312_log
#print axioms leaf00312_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
