/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00290 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 387040666485669095560535290675200000000000 464242482029742459707570716302800584704 885050383145043911636733132800000000000))
theorem leaf00290_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 387040666485669095560535290675200000000000 464242482029742459707570716302800584704 885050383145043911636733132800000000000 raw00290=true := by decide +kernel
#print axioms leaf00290_raw
theorem leaf00290_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00290=true := by decide +kernel
#print axioms leaf00290_rectangular
def affine00290 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00290 (IntegerComputedClassCell.leftNumerator ![(21/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(21/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(21/3200),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00290_transform : affine00290=(NestedInteger.clearedAll 3 raw00290 (IntegerComputedClassCell.leftNumerator ![(21/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(21/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(21/3200),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00290_transform
theorem leaf00290_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00290=true := by decide +kernel
#print axioms leaf00290_sign
theorem leaf00290_log : RationalLog.accepts (3379169/4294967296) (-15349288795/4294967296) 11 8=true := by decide +kernel
#print axioms leaf00290_log
def leaf00290 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (104907582861/200000000000) (3379169/4294967296) (-15349288795/4294967296) 11 8 ![60,0,4] ![(21/3200),0,0] ![(1/6400),1,(1/16)] affine00290
theorem leaf00290_checked : FastNestedCellData.accepts 1 2 4 leaf00290=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (104907582861/200000000000) (3379169/4294967296) (-15349288795/4294967296) 11 8 ![60,0,4] ![(21/3200),0,0] ![(1/6400),1,(1/16)] 387040666485669095560535290675200000000000 464242482029742459707570716302800584704 885050383145043911636733132800000000000 raw00290 affine00290
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00290_raw leaf00290_rectangular
    leaf00290_transform leaf00290_sign leaf00290_log
#print axioms leaf00290_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
