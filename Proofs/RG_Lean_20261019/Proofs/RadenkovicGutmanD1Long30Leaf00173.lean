/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00173 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 8191459559857817793318617088000000000000 7665425464060053661202102310120191950848 269720975697191666599145242624000000000000))
theorem leaf00173_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 8191459559857817793318617088000000000000 7665425464060053661202102310120191950848 269720975697191666599145242624000000000000 raw00173=true := by decide +kernel
#print axioms leaf00173_raw
theorem leaf00173_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00173=true := by decide +kernel
#print axioms leaf00173_rectangular
def affine00173 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00173 (IntegerComputedClassCell.leftNumerator ![(59/16000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(59/16000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(59/16000),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00173_transform : affine00173=(NestedInteger.clearedAll 3 raw00173 (IntegerComputedClassCell.leftNumerator ![(59/16000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(59/16000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(59/16000),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00173_transform
theorem leaf00173_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00173=true := by decide +kernel
#print axioms leaf00173_sign
theorem leaf00173_log : RationalLog.accepts (977022127/1073741824) (-50678239/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00173_log
def leaf00173 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (14209917201/500000000000) (977022127/1073741824) (-50678239/1073741824) 1 8 ![60,0,4] ![(59/16000),0,(1/4)] ![(3/32000),1,(1/4)] affine00173
theorem leaf00173_checked : FastNestedCellData.accepts 1 2 4 leaf00173=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (14209917201/500000000000) (977022127/1073741824) (-50678239/1073741824) 1 8 ![60,0,4] ![(59/16000),0,(1/4)] ![(3/32000),1,(1/4)] 8191459559857817793318617088000000000000 7665425464060053661202102310120191950848 269720975697191666599145242624000000000000 raw00173 affine00173
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00173_raw leaf00173_rectangular
    leaf00173_transform leaf00173_sign leaf00173_log
#print axioms leaf00173_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
