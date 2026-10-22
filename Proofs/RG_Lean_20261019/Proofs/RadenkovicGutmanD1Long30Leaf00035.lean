/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00035 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 39985475981952629878021947392000000000000 815341180218107857356603962450509824 5877286422007715639328768000000000000))
theorem leaf00035_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 39985475981952629878021947392000000000000 815341180218107857356603962450509824 5877286422007715639328768000000000000 raw00035=true := by decide +kernel
#print axioms leaf00035_raw
theorem leaf00035_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00035=true := by decide +kernel
#print axioms leaf00035_rectangular
def affine00035 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00035 (IntegerComputedClassCell.leftNumerator ![(23/16000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/16000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/16000),0,0] ![(1/16000),1,(1/16)]))
theorem leaf00035_transform : affine00035=(NestedInteger.clearedAll 3 raw00035 (IntegerComputedClassCell.leftNumerator ![(23/16000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/16000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/16000),0,0] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00035_transform
theorem leaf00035_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00035=true := by decide +kernel
#print axioms leaf00035_sign
theorem leaf00035_log : RationalLog.accepts (76909/4294967296) (-11736354465/2147483648) 16 8=true := by decide +kernel
#print axioms leaf00035_log
def leaf00035 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (17340935971/125000000000) (76909/4294967296) (-11736354465/2147483648) 16 8 ![60,0,4] ![(23/16000),0,0] ![(1/16000),1,(1/16)] affine00035
theorem leaf00035_checked : FastNestedCellData.accepts 1 2 4 leaf00035=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (17340935971/125000000000) (76909/4294967296) (-11736354465/2147483648) 16 8 ![60,0,4] ![(23/16000),0,0] ![(1/16000),1,(1/16)] 39985475981952629878021947392000000000000 815341180218107857356603962450509824 5877286422007715639328768000000000000 raw00035 affine00035
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00035_raw leaf00035_rectangular
    leaf00035_transform leaf00035_sign leaf00035_log
#print axioms leaf00035_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
