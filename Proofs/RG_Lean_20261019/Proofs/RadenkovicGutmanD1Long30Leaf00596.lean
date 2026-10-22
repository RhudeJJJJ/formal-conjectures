/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00596 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 9111989238844735335867493646336000000000000 3156368515421940062644047641866924235685888 6389902432949439788143375024128000000000000))
theorem leaf00596_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 9111989238844735335867493646336000000000000 3156368515421940062644047641866924235685888 6389902432949439788143375024128000000000000 raw00596=true := by decide +kernel
#print axioms leaf00596_raw
theorem leaf00596_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00596=true := by decide +kernel
#print axioms leaf00596_rectangular
def affine00596 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00596 (IntegerComputedClassCell.leftNumerator ![(31/1600),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/1600),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/1600),0,(1/16)] ![(1/3200),1,(1/16)]))
theorem leaf00596_transform : affine00596=(NestedInteger.clearedAll 3 raw00596 (IntegerComputedClassCell.leftNumerator ![(31/1600),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/1600),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/1600),0,(1/16)] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00596_transform
theorem leaf00596_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00596=true := by decide +kernel
#print axioms leaf00596_sign
theorem leaf00596_log : RationalLog.accepts (995852083/4294967296) (-3138763247/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00596_log
def leaf00596 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (493961926421/1000000000000) (995852083/4294967296) (-3138763247/4294967296) 3 8 ![60,0,4] ![(31/1600),0,(1/16)] ![(1/3200),1,(1/16)] affine00596
theorem leaf00596_checked : FastNestedCellData.accepts 1 2 4 leaf00596=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (493961926421/1000000000000) (995852083/4294967296) (-3138763247/4294967296) 3 8 ![60,0,4] ![(31/1600),0,(1/16)] ![(1/3200),1,(1/16)] 9111989238844735335867493646336000000000000 3156368515421940062644047641866924235685888 6389902432949439788143375024128000000000000 raw00596 affine00596
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00596_raw leaf00596_rectangular
    leaf00596_transform leaf00596_sign leaf00596_log
#print axioms leaf00596_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
