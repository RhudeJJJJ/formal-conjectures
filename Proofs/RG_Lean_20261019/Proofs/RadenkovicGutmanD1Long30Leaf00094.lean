/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00094 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1902017864225936907048478310400000000000 1864416310665534508454530258581697069056 226025811695606327128126128128000000000000))
theorem leaf00094_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1902017864225936907048478310400000000000 1864416310665534508454530258581697069056 226025811695606327128126128128000000000000 raw00094=true := by decide +kernel
#print axioms leaf00094_raw
theorem leaf00094_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00094=true := by decide +kernel
#print axioms leaf00094_rectangular
def affine00094 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00094 (IntegerComputedClassCell.leftNumerator ![(7/3200),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/3200),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/3200),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00094_transform : affine00094=(NestedInteger.clearedAll 3 raw00094 (IntegerComputedClassCell.leftNumerator ![(7/3200),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/3200),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/3200),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00094_transform
theorem leaf00094_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00094=true := by decide +kernel
#print axioms leaf00094_sign
theorem leaf00094_log : RationalLog.accepts (2087807735/2147483648) (-30260399/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00094_log
def leaf00094 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (4124343801/500000000000) (2087807735/2147483648) (-30260399/2147483648) 1 8 ![60,0,4] ![(7/3200),0,(1/2)] ![(3/32000),1,(1/2)] affine00094
theorem leaf00094_checked : FastNestedCellData.accepts 1 2 4 leaf00094=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (4124343801/500000000000) (2087807735/2147483648) (-30260399/2147483648) 1 8 ![60,0,4] ![(7/3200),0,(1/2)] ![(3/32000),1,(1/2)] 1902017864225936907048478310400000000000 1864416310665534508454530258581697069056 226025811695606327128126128128000000000000 raw00094 affine00094
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00094_raw leaf00094_rectangular
    leaf00094_transform leaf00094_sign leaf00094_log
#print axioms leaf00094_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
