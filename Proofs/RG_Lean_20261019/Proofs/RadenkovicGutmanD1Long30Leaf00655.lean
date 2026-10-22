/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00655 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 15868008269878296855235553918976000000000000 357883147020975225584935468261178855129088 416043318676713337431846289408000000000000))
theorem leaf00655_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 15868008269878296855235553918976000000000000 357883147020975225584935468261178855129088 416043318676713337431846289408000000000000 raw00655=true := by decide +kernel
#print axioms leaf00655_raw
theorem leaf00655_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00655=true := by decide +kernel
#print axioms leaf00655_rectangular
def affine00655 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00655 (IntegerComputedClassCell.leftNumerator ![(79/3200),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(79/3200),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(79/3200),0,0] ![(3/6400),1,(1/16)]))
theorem leaf00655_transform : affine00655=(NestedInteger.clearedAll 3 raw00655 (IntegerComputedClassCell.leftNumerator ![(79/3200),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(79/3200),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(79/3200),0,0] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00655_transform
theorem leaf00655_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00655=true := by decide +kernel
#print axioms leaf00655_sign
theorem leaf00655_log : RationalLog.accepts (52073593/4294967296) (-592241277/268435456) 7 8=true := by decide +kernel
#print axioms leaf00655_log
def leaf00655 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (860206451961/1000000000000) (52073593/4294967296) (-592241277/268435456) 7 8 ![60,0,4] ![(79/3200),0,0] ![(3/6400),1,(1/16)] affine00655
theorem leaf00655_checked : FastNestedCellData.accepts 1 2 4 leaf00655=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (860206451961/1000000000000) (52073593/4294967296) (-592241277/268435456) 7 8 ![60,0,4] ![(79/3200),0,0] ![(3/6400),1,(1/16)] 15868008269878296855235553918976000000000000 357883147020975225584935468261178855129088 416043318676713337431846289408000000000000 raw00655 affine00655
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00655_raw leaf00655_rectangular
    leaf00655_transform leaf00655_sign leaf00655_log
#print axioms leaf00655_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
