/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00574 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 336508266409028873056210124800000000000 290593355775814833281934986344245755904 4424937742672753793474284748800000000000))
theorem leaf00574_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 336508266409028873056210124800000000000 290593355775814833281934986344245755904 4424937742672753793474284748800000000000 raw00574=true := by decide +kernel
#print axioms leaf00574_raw
theorem leaf00574_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00574=true := by decide +kernel
#print axioms leaf00574_rectangular
def affine00574 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00574 (IntegerComputedClassCell.leftNumerator ![(57/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(57/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(57/3200),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00574_transform : affine00574=(NestedInteger.clearedAll 3 raw00574 (IntegerComputedClassCell.leftNumerator ![(57/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(57/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(57/3200),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00574_transform
theorem leaf00574_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00574=true := by decide +kernel
#print axioms leaf00574_sign
theorem leaf00574_log : RationalLog.accepts (1740188763/2147483648) (-451622651/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00574_log
def leaf00574 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (6567173883/100000000000) (1740188763/2147483648) (-451622651/4294967296) 1 8 ![60,0,4] ![(57/3200),0,(1/2)] ![(1/3200),1,(1/2)] affine00574
theorem leaf00574_checked : FastNestedCellData.accepts 1 2 4 leaf00574=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (6567173883/100000000000) (1740188763/2147483648) (-451622651/4294967296) 1 8 ![60,0,4] ![(57/3200),0,(1/2)] ![(1/3200),1,(1/2)] 336508266409028873056210124800000000000 290593355775814833281934986344245755904 4424937742672753793474284748800000000000 raw00574 affine00574
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00574_raw leaf00574_rectangular
    leaf00574_transform leaf00574_sign leaf00574_log
#print axioms leaf00574_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
