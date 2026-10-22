/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00561 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2104605042857454190617744637952000000000000 786578864935048094448993494216263549845504 1723579807110219466666313515008000000000000))
theorem leaf00561_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2104605042857454190617744637952000000000000 786578864935048094448993494216263549845504 1723579807110219466666313515008000000000000 raw00561=true := by decide +kernel
#print axioms leaf00561_raw
theorem leaf00561_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00561=true := by decide +kernel
#print axioms leaf00561_rectangular
def affine00561 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00561 (IntegerComputedClassCell.leftNumerator ![(11/640),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/640),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/640),0,(1/16)] ![(1/3200),1,(1/16)]))
theorem leaf00561_transform : affine00561=(NestedInteger.clearedAll 3 raw00561 (IntegerComputedClassCell.leftNumerator ![(11/640),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/640),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/640),0,(1/16)] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00561_transform
theorem leaf00561_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00561=true := by decide +kernel
#print axioms leaf00561_sign
theorem leaf00561_log : RationalLog.accepts (1102203409/4294967296) (-2920862729/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00561_log
def leaf00561 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (228181735969/500000000000) (1102203409/4294967296) (-2920862729/4294967296) 2 8 ![60,0,4] ![(11/640),0,(1/16)] ![(1/3200),1,(1/16)] affine00561
theorem leaf00561_checked : FastNestedCellData.accepts 1 2 4 leaf00561=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (228181735969/500000000000) (1102203409/4294967296) (-2920862729/4294967296) 2 8 ![60,0,4] ![(11/640),0,(1/16)] ![(1/3200),1,(1/16)] 2104605042857454190617744637952000000000000 786578864935048094448993494216263549845504 1723579807110219466666313515008000000000000 raw00561 affine00561
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00561_raw leaf00561_rectangular
    leaf00561_transform leaf00561_sign leaf00561_log
#print axioms leaf00561_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
