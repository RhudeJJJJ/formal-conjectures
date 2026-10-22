/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00565 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 149992536341439794254725932646400000000000 1658780726342002013873907524614695682048 2040041743382337895280096051200000000000))
theorem leaf00565_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 149992536341439794254725932646400000000000 1658780726342002013873907524614695682048 2040041743382337895280096051200000000000 raw00565=true := by decide +kernel
#print axioms leaf00565_raw
theorem leaf00565_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00565=true := by decide +kernel
#print axioms leaf00565_rectangular
def affine00565 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00565 (IntegerComputedClassCell.leftNumerator ![(7/400),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/400),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/400),0,0] ![(1/3200),1,(1/16)]))
theorem leaf00565_transform : affine00565=(NestedInteger.clearedAll 3 raw00565 (IntegerComputedClassCell.leftNumerator ![(7/400),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/400),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/400),0,0] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00565_transform
theorem leaf00565_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00565=true := by decide +kernel
#print axioms leaf00565_sign
theorem leaf00565_log : RationalLog.accepts (26197193/4294967296) (-10951193975/4294967296) 8 8=true := by decide +kernel
#print axioms leaf00565_log
def leaf00565 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (81311116879/100000000000) (26197193/4294967296) (-10951193975/4294967296) 8 8 ![60,0,4] ![(7/400),0,0] ![(1/3200),1,(1/16)] affine00565
theorem leaf00565_checked : FastNestedCellData.accepts 1 2 4 leaf00565=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (81311116879/100000000000) (26197193/4294967296) (-10951193975/4294967296) 8 8 ![60,0,4] ![(7/400),0,0] ![(1/3200),1,(1/16)] 149992536341439794254725932646400000000000 1658780726342002013873907524614695682048 2040041743382337895280096051200000000000 raw00565 affine00565
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00565_raw leaf00565_rectangular
    leaf00565_transform leaf00565_sign leaf00565_log
#print axioms leaf00565_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
