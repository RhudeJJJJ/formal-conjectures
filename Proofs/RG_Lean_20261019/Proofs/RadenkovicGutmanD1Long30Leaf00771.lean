/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00771 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 38601244619805488250652668723200000000000 9803716434519243637582689185569318109184 14640610184659060065048723456000000000000))
theorem leaf00771_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 38601244619805488250652668723200000000000 9803716434519243637582689185569318109184 14640610184659060065048723456000000000000 raw00771=true := by decide +kernel
#print axioms leaf00771_raw
theorem leaf00771_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00771=true := by decide +kernel
#print axioms leaf00771_rectangular
def affine00771 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00771 (IntegerComputedClassCell.leftNumerator ![(59/1600),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(59/1600),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(59/1600),0,(1/16)] ![(3/3200),1,(1/16)]))
theorem leaf00771_transform : affine00771=(NestedInteger.clearedAll 3 raw00771 (IntegerComputedClassCell.leftNumerator ![(59/1600),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(59/1600),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(59/1600),0,(1/16)] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00771_transform
theorem leaf00771_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00771=true := by decide +kernel
#print axioms leaf00771_sign
theorem leaf00771_log : RationalLog.accepts (81665835/536870912) (-252748355/268435456) 3 8=true := by decide +kernel
#print axioms leaf00771_log
def leaf00771 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (669624852439/1000000000000) (81665835/536870912) (-252748355/268435456) 3 8 ![60,0,4] ![(59/1600),0,(1/16)] ![(3/3200),1,(1/16)] affine00771
theorem leaf00771_checked : FastNestedCellData.accepts 1 2 4 leaf00771=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (669624852439/1000000000000) (81665835/536870912) (-252748355/268435456) 3 8 ![60,0,4] ![(59/1600),0,(1/16)] ![(3/3200),1,(1/16)] 38601244619805488250652668723200000000000 9803716434519243637582689185569318109184 14640610184659060065048723456000000000000 raw00771 affine00771
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00771_raw leaf00771_rectangular
    leaf00771_transform leaf00771_sign leaf00771_log
#print axioms leaf00771_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
