/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00478 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 431020196531886106050897641472000000000000 350157510212119222576757013829842597052416 3746498440411513920033193459712000000000000))
theorem leaf00478_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 431020196531886106050897641472000000000000 350157510212119222576757013829842597052416 3746498440411513920033193459712000000000000 raw00478=true := by decide +kernel
#print axioms leaf00478_raw
theorem leaf00478_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00478=true := by decide +kernel
#print axioms leaf00478_rectangular
def affine00478 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00478 (IntegerComputedClassCell.leftNumerator ![(79/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(79/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(79/6400),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00478_transform : affine00478=(NestedInteger.clearedAll 3 raw00478 (IntegerComputedClassCell.leftNumerator ![(79/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(79/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(79/6400),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00478_transform
theorem leaf00478_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00478=true := by decide +kernel
#print axioms leaf00478_sign
theorem leaf00478_log : RationalLog.accepts (1595481433/2147483648) (-159515755/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00478_log
def leaf00478 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (93462606693/1000000000000) (1595481433/2147483648) (-159515755/1073741824) 1 8 ![60,0,4] ![(79/6400),0,(1/4)] ![(1/6400),1,(1/4)] affine00478
theorem leaf00478_checked : FastNestedCellData.accepts 1 2 4 leaf00478=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (93462606693/1000000000000) (1595481433/2147483648) (-159515755/1073741824) 1 8 ![60,0,4] ![(79/6400),0,(1/4)] ![(1/6400),1,(1/4)] 431020196531886106050897641472000000000000 350157510212119222576757013829842597052416 3746498440411513920033193459712000000000000 raw00478 affine00478
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00478_raw leaf00478_rectangular
    leaf00478_transform leaf00478_sign leaf00478_log
#print axioms leaf00478_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
