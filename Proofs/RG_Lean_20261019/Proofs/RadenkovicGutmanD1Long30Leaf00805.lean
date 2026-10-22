/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00805 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 40581562255943784980528339353600000000000 2795964400017136660491275095512782471168 3177332072692990422511989555200000000000))
theorem leaf00805_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 40581562255943784980528339353600000000000 2795964400017136660491275095512782471168 3177332072692990422511989555200000000000 raw00805=true := by decide +kernel
#print axioms leaf00805_raw
theorem leaf00805_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00805=true := by decide +kernel
#print axioms leaf00805_rectangular
def affine00805 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00805 (IntegerComputedClassCell.leftNumerator ![(139/3200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(139/3200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(139/3200),0,0] ![(3/3200),1,(1/16)]))
theorem leaf00805_transform : affine00805=(NestedInteger.clearedAll 3 raw00805 (IntegerComputedClassCell.leftNumerator ![(139/3200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(139/3200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(139/3200),0,0] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00805_transform
theorem leaf00805_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00805=true := by decide +kernel
#print axioms leaf00805_sign
theorem leaf00805_log : RationalLog.accepts (39350593/1073741824) (-7100426827/4294967296) 5 8=true := by decide +kernel
#print axioms leaf00805_log
def leaf00805 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (175994471843/200000000000) (39350593/1073741824) (-7100426827/4294967296) 5 8 ![60,0,4] ![(139/3200),0,0] ![(3/3200),1,(1/16)] affine00805
theorem leaf00805_checked : FastNestedCellData.accepts 1 2 4 leaf00805=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (175994471843/200000000000) (39350593/1073741824) (-7100426827/4294967296) 5 8 ![60,0,4] ![(139/3200),0,0] ![(3/3200),1,(1/16)] 40581562255943784980528339353600000000000 2795964400017136660491275095512782471168 3177332072692990422511989555200000000000 raw00805 affine00805
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00805_raw leaf00805_rectangular
    leaf00805_transform leaf00805_sign leaf00805_log
#print axioms leaf00805_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
