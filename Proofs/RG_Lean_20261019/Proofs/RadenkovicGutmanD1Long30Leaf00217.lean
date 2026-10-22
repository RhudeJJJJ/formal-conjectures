/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00217 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 81774886627461884435249496064000000000000 69564622955135403861530167012948963229696 980772374900595188398360100864000000000000))
theorem leaf00217_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 81774886627461884435249496064000000000000 69564622955135403861530167012948963229696 980772374900595188398360100864000000000000 raw00217=true := by decide +kernel
#print axioms leaf00217_raw
theorem leaf00217_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00217=true := by decide +kernel
#print axioms leaf00217_rectangular
def affine00217 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00217 (IntegerComputedClassCell.leftNumerator ![(29/6400),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(29/6400),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(29/6400),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00217_transform : affine00217=(NestedInteger.clearedAll 3 raw00217 (IntegerComputedClassCell.leftNumerator ![(29/6400),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(29/6400),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(29/6400),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00217_transform
theorem leaf00217_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00217=true := by decide +kernel
#print axioms leaf00217_sign
theorem leaf00217_log : RationalLog.accepts (852919249/1073741824) (-247218317/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00217_log
def leaf00217 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (70928407789/1000000000000) (852919249/1073741824) (-247218317/2147483648) 1 8 ![60,0,4] ![(29/6400),0,(1/8)] ![(3/32000),1,(1/8)] affine00217
theorem leaf00217_checked : FastNestedCellData.accepts 1 2 4 leaf00217=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (70928407789/1000000000000) (852919249/1073741824) (-247218317/2147483648) 1 8 ![60,0,4] ![(29/6400),0,(1/8)] ![(3/32000),1,(1/8)] 81774886627461884435249496064000000000000 69564622955135403861530167012948963229696 980772374900595188398360100864000000000000 raw00217 affine00217
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00217_raw leaf00217_rectangular
    leaf00217_transform leaf00217_sign leaf00217_log
#print axioms leaf00217_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
