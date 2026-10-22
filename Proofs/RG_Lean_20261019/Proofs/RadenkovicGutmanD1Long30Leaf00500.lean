/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00500 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3487774679233597706178702344192000000000000 21893255333573298365781040370607238152192 28948205892098164425599483904000000000000))
theorem leaf00500_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3487774679233597706178702344192000000000000 21893255333573298365781040370607238152192 28948205892098164425599483904000000000000 raw00500=true := by decide +kernel
#print axioms leaf00500_raw
theorem leaf00500_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00500=true := by decide +kernel
#print axioms leaf00500_rectangular
def affine00500 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00500 (IntegerComputedClassCell.leftNumerator ![(43/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(43/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(43/3200),0,0] ![(1/3200),1,(1/16)]))
theorem leaf00500_transform : affine00500=(NestedInteger.clearedAll 3 raw00500 (IntegerComputedClassCell.leftNumerator ![(43/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(43/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(43/3200),0,0] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00500_transform
theorem leaf00500_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00500=true := by decide +kernel
#print axioms leaf00500_sign
theorem leaf00500_log : RationalLog.accepts (7675301/2147483648) (-12099018815/4294967296) 9 8=true := by decide +kernel
#print axioms leaf00500_log
def leaf00500 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (756290576873/1000000000000) (7675301/2147483648) (-12099018815/4294967296) 9 8 ![60,0,4] ![(43/3200),0,0] ![(1/3200),1,(1/16)] affine00500
theorem leaf00500_checked : FastNestedCellData.accepts 1 2 4 leaf00500=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (756290576873/1000000000000) (7675301/2147483648) (-12099018815/4294967296) 9 8 ![60,0,4] ![(43/3200),0,0] ![(1/3200),1,(1/16)] 3487774679233597706178702344192000000000000 21893255333573298365781040370607238152192 28948205892098164425599483904000000000000 raw00500 affine00500
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00500_raw leaf00500_rectangular
    leaf00500_transform leaf00500_sign leaf00500_log
#print axioms leaf00500_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
