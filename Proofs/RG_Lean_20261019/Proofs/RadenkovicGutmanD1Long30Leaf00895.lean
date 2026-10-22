/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00895 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 627612220008807992268496148889600000000000 96732218949244285804676225053894826262528 113725923731294103409739903795200000000000))
theorem leaf00895_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 627612220008807992268496148889600000000000 96732218949244285804676225053894826262528 113725923731294103409739903795200000000000 raw00895=true := by decide +kernel
#print axioms leaf00895_raw
theorem leaf00895_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00895=true := by decide +kernel
#print axioms leaf00895_rectangular
def affine00895 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00895 (IntegerComputedClassCell.leftNumerator ![(43/640),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(43/640),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(43/640),0,0] ![(1/640),1,(1/16)]))
theorem leaf00895_transform : affine00895=(NestedInteger.clearedAll 3 raw00895 (IntegerComputedClassCell.leftNumerator ![(43/640),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(43/640),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(43/640),0,0] ![(1/640),1,(1/16)])) := by decide +kernel
#print axioms leaf00895_transform
theorem leaf00895_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00895=true := by decide +kernel
#print axioms leaf00895_sign
theorem leaf00895_log : RationalLog.accepts (357711877/4294967296) (-5337509267/4294967296) 4 8=true := by decide +kernel
#print axioms leaf00895_log
def leaf00895 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (170114633103/200000000000) (357711877/4294967296) (-5337509267/4294967296) 4 8 ![60,0,4] ![(43/640),0,0] ![(1/640),1,(1/16)] affine00895
theorem leaf00895_checked : FastNestedCellData.accepts 1 2 4 leaf00895=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (170114633103/200000000000) (357711877/4294967296) (-5337509267/4294967296) 4 8 ![60,0,4] ![(43/640),0,0] ![(1/640),1,(1/16)] 627612220008807992268496148889600000000000 96732218949244285804676225053894826262528 113725923731294103409739903795200000000000 raw00895 affine00895
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00895_raw leaf00895_rectangular
    leaf00895_transform leaf00895_sign leaf00895_log
#print axioms leaf00895_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
