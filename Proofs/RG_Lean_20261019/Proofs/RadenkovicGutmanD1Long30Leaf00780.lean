/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00780 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 63492481199477682702445969408000000000000 3510176699092233492284874741268856438784 3983698271137383763912163328000000000000))
theorem leaf00780_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 63492481199477682702445969408000000000000 3510176699092233492284874741268856438784 3983698271137383763912163328000000000000 raw00780=true := by decide +kernel
#print axioms leaf00780_raw
theorem leaf00780_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00780=true := by decide +kernel
#print axioms leaf00780_rectangular
def affine00780 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00780 (IntegerComputedClassCell.leftNumerator ![(31/800),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/800),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/800),0,0] ![(3/3200),1,(1/16)]))
theorem leaf00780_transform : affine00780=(NestedInteger.clearedAll 3 raw00780 (IntegerComputedClassCell.leftNumerator ![(31/800),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/800),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/800),0,0] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00780_transform
theorem leaf00780_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00780=true := by decide +kernel
#print axioms leaf00780_sign
theorem leaf00780_log : RationalLog.accepts (15778167/536870912) (-1893613837/1073741824) 6 8=true := by decide +kernel
#print axioms leaf00780_log
def leaf00780 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (440567590739/500000000000) (15778167/536870912) (-1893613837/1073741824) 6 8 ![60,0,4] ![(31/800),0,0] ![(3/3200),1,(1/16)] affine00780
theorem leaf00780_checked : FastNestedCellData.accepts 1 2 4 leaf00780=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (440567590739/500000000000) (15778167/536870912) (-1893613837/1073741824) 6 8 ![60,0,4] ![(31/800),0,0] ![(3/3200),1,(1/16)] 63492481199477682702445969408000000000000 3510176699092233492284874741268856438784 3983698271137383763912163328000000000000 raw00780 affine00780
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00780_raw leaf00780_rectangular
    leaf00780_transform leaf00780_sign leaf00780_log
#print axioms leaf00780_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
