/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00942 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 11051025779253537580850503221248000000000000 4702771705214852512978753818624191914573824 7850024768383156511599868510208000000000000))
theorem leaf00942_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 11051025779253537580850503221248000000000000 4702771705214852512978753818624191914573824 7850024768383156511599868510208000000000000 raw00942=true := by decide +kernel
#print axioms leaf00942_raw
theorem leaf00942_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00942=true := by decide +kernel
#print axioms leaf00942_rectangular
def affine00942 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00942 (IntegerComputedClassCell.leftNumerator ![(29/320),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(29/320),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.denominator ![(29/320),0,(1/8)] ![(1/320),1,(1/8)]))
theorem leaf00942_transform : affine00942=(NestedInteger.clearedAll 3 raw00942 (IntegerComputedClassCell.leftNumerator ![(29/320),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(29/320),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.denominator ![(29/320),0,(1/8)] ![(1/320),1,(1/8)])) := by decide +kernel
#print axioms leaf00942_transform
theorem leaf00942_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00942=true := by decide +kernel
#print axioms leaf00942_sign
theorem leaf00942_log : RationalLog.accepts (1142988091/4294967296) (-177677161/268435456) 2 8=true := by decide +kernel
#print axioms leaf00942_log
def leaf00942 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (599077307903/1000000000000) (1142988091/4294967296) (-177677161/268435456) 2 8 ![60,0,4] ![(29/320),0,(1/8)] ![(1/320),1,(1/8)] affine00942
theorem leaf00942_checked : FastNestedCellData.accepts 1 2 4 leaf00942=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (599077307903/1000000000000) (1142988091/4294967296) (-177677161/268435456) 2 8 ![60,0,4] ![(29/320),0,(1/8)] ![(1/320),1,(1/8)] 11051025779253537580850503221248000000000000 4702771705214852512978753818624191914573824 7850024768383156511599868510208000000000000 raw00942 affine00942
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00942_raw leaf00942_rectangular
    leaf00942_transform leaf00942_sign leaf00942_log
#print axioms leaf00942_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
