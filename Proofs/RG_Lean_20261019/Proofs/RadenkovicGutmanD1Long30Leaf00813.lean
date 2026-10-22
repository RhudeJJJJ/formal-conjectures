/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00813 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 8707118673225324692229094113280000000000 4976342801093663250872571417442457223168 16868463705607044815643853455360000000000))
theorem leaf00813_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 8707118673225324692229094113280000000000 4976342801093663250872571417442457223168 16868463705607044815643853455360000000000 raw00813=true := by decide +kernel
#print axioms leaf00813_raw
theorem leaf00813_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00813=true := by decide +kernel
#print axioms leaf00813_rectangular
def affine00813 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00813 (IntegerComputedClassCell.leftNumerator ![(71/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(71/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(71/1600),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00813_transform : affine00813=(NestedInteger.clearedAll 3 raw00813 (IntegerComputedClassCell.leftNumerator ![(71/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(71/1600),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(71/1600),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00813_transform
theorem leaf00813_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00813=true := by decide +kernel
#print axioms leaf00813_sign
theorem leaf00813_log : RationalLog.accepts (1895496627/4294967296) (-1756562377/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00813_log
def leaf00813 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (11800346227/40000000000) (1895496627/4294967296) (-1756562377/4294967296) 2 8 ![60,0,4] ![(71/1600),0,(1/4)] ![(3/3200),1,(1/4)] affine00813
theorem leaf00813_checked : FastNestedCellData.accepts 1 2 4 leaf00813=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (11800346227/40000000000) (1895496627/4294967296) (-1756562377/4294967296) 2 8 ![60,0,4] ![(71/1600),0,(1/4)] ![(3/3200),1,(1/4)] 8707118673225324692229094113280000000000 4976342801093663250872571417442457223168 16868463705607044815643853455360000000000 raw00813 affine00813
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00813_raw leaf00813_rectangular
    leaf00813_transform leaf00813_sign leaf00813_log
#print axioms leaf00813_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
