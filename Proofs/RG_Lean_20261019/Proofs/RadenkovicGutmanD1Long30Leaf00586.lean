/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00586 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2230592811325817284597882290176000000000000 788817938380021666695466850319094234742784 1630858235999443886910719655936000000000000))
theorem leaf00586_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2230592811325817284597882290176000000000000 788817938380021666695466850319094234742784 1630858235999443886910719655936000000000000 raw00586=true := by decide +kernel
#print axioms leaf00586_raw
theorem leaf00586_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00586=true := by decide +kernel
#print axioms leaf00586_rectangular
def affine00586 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00586 (IntegerComputedClassCell.leftNumerator ![(3/160),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/160),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/160),0,(1/16)] ![(1/3200),1,(1/16)]))
theorem leaf00586_transform : affine00586=(NestedInteger.clearedAll 3 raw00586 (IntegerComputedClassCell.leftNumerator ![(3/160),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/160),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/160),0,(1/16)] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00586_transform
theorem leaf00586_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00586=true := by decide +kernel
#print axioms leaf00586_sign
theorem leaf00586_log : RationalLog.accepts (1023706131/4294967296) (-3079522661/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00586_log
def leaf00586 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (241841357197/500000000000) (1023706131/4294967296) (-3079522661/4294967296) 3 8 ![60,0,4] ![(3/160),0,(1/16)] ![(1/3200),1,(1/16)] affine00586
theorem leaf00586_checked : FastNestedCellData.accepts 1 2 4 leaf00586=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (241841357197/500000000000) (1023706131/4294967296) (-3079522661/4294967296) 3 8 ![60,0,4] ![(3/160),0,(1/16)] ![(1/3200),1,(1/16)] 2230592811325817284597882290176000000000000 788817938380021666695466850319094234742784 1630858235999443886910719655936000000000000 raw00586 affine00586
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00586_raw leaf00586_rectangular
    leaf00586_transform leaf00586_sign leaf00586_log
#print axioms leaf00586_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
