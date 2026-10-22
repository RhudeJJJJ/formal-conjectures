/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00579 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 16427461305643275077873880268800000000000 14153785301963418689724548954641737449472 211914468731581937300303721267200000000000))
theorem leaf00579_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 16427461305643275077873880268800000000000 14153785301963418689724548954641737449472 211914468731581937300303721267200000000000 raw00579=true := by decide +kernel
#print axioms leaf00579_raw
theorem leaf00579_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00579=true := by decide +kernel
#print axioms leaf00579_rectangular
def affine00579 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00579 (IntegerComputedClassCell.leftNumerator ![(29/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(29/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(29/1600),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00579_transform : affine00579=(NestedInteger.clearedAll 3 raw00579 (IntegerComputedClassCell.leftNumerator ![(29/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(29/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(29/1600),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00579_transform
theorem leaf00579_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00579=true := by decide +kernel
#print axioms leaf00579_sign
theorem leaf00579_log : RationalLog.accepts (3468830199/4294967296) (-458759499/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00579_log
def leaf00579 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (13358016927/200000000000) (3468830199/4294967296) (-458759499/4294967296) 1 8 ![60,0,4] ![(29/1600),0,(1/2)] ![(1/3200),1,(1/2)] affine00579
theorem leaf00579_checked : FastNestedCellData.accepts 1 2 4 leaf00579=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (13358016927/200000000000) (3468830199/4294967296) (-458759499/4294967296) 1 8 ![60,0,4] ![(29/1600),0,(1/2)] ![(1/3200),1,(1/2)] 16427461305643275077873880268800000000000 14153785301963418689724548954641737449472 211914468731581937300303721267200000000000 raw00579 affine00579
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00579_raw leaf00579_rectangular
    leaf00579_transform leaf00579_sign leaf00579_log
#print axioms leaf00579_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
