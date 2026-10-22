/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00516 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 11837625973260621822347888820224000000000 4952841056915988064206723920328627585024 12348934371951554647488567705600000000000))
theorem leaf00516_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 11837625973260621822347888820224000000000 4952841056915988064206723920328627585024 12348934371951554647488567705600000000000 raw00516=true := by decide +kernel
#print axioms leaf00516_raw
theorem leaf00516_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00516=true := by decide +kernel
#print axioms leaf00516_rectangular
def affine00516 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00516 (IntegerComputedClassCell.leftNumerator ![(23/1600),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/1600),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/1600),0,(1/16)] ![(1/3200),1,(1/16)]))
theorem leaf00516_transform : affine00516=(NestedInteger.clearedAll 3 raw00516 (IntegerComputedClassCell.leftNumerator ![(23/1600),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/1600),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/1600),0,(1/16)] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00516_transform
theorem leaf00516_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00516=true := by decide +kernel
#print axioms leaf00516_sign
theorem leaf00516_log : RationalLog.accepts (1282591775/4294967296) (-2595365241/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00516_log
def leaf00516 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (80214873733/200000000000) (1282591775/4294967296) (-2595365241/4294967296) 2 8 ![60,0,4] ![(23/1600),0,(1/16)] ![(1/3200),1,(1/16)] affine00516
theorem leaf00516_checked : FastNestedCellData.accepts 1 2 4 leaf00516=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (80214873733/200000000000) (1282591775/4294967296) (-2595365241/4294967296) 2 8 ![60,0,4] ![(23/1600),0,(1/16)] ![(1/3200),1,(1/16)] 11837625973260621822347888820224000000000 4952841056915988064206723920328627585024 12348934371951554647488567705600000000000 raw00516 affine00516
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00516_raw leaf00516_rectangular
    leaf00516_transform leaf00516_sign leaf00516_log
#print axioms leaf00516_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
