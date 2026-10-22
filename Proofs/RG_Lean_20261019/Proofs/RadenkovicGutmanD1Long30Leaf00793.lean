/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00793 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 106139539411214888243505922048000000000000 62154269263841666299192509558931197001728 225046493935937264985374195712000000000000))
theorem leaf00793_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 106139539411214888243505922048000000000000 62154269263841666299192509558931197001728 225046493935937264985374195712000000000000 raw00793=true := by decide +kernel
#print axioms leaf00793_raw
theorem leaf00793_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00793=true := by decide +kernel
#print axioms leaf00793_rectangular
def affine00793 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00793 (IntegerComputedClassCell.leftNumerator ![(13/320),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/320),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/320),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00793_transform : affine00793=(NestedInteger.clearedAll 3 raw00793 (IntegerComputedClassCell.leftNumerator ![(13/320),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/320),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/320),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00793_transform
theorem leaf00793_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00793=true := by decide +kernel
#print axioms leaf00793_sign
theorem leaf00793_log : RationalLog.accepts (492697431/1073741824) (-209113807/536870912) 2 8=true := by decide +kernel
#print axioms leaf00793_log
def leaf00793 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (276184126119/1000000000000) (492697431/1073741824) (-209113807/536870912) 2 8 ![60,0,4] ![(13/320),0,(1/4)] ![(3/3200),1,(1/4)] affine00793
theorem leaf00793_checked : FastNestedCellData.accepts 1 2 4 leaf00793=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (276184126119/1000000000000) (492697431/1073741824) (-209113807/536870912) 2 8 ![60,0,4] ![(13/320),0,(1/4)] ![(3/3200),1,(1/4)] 106139539411214888243505922048000000000000 62154269263841666299192509558931197001728 225046493935937264985374195712000000000000 raw00793 affine00793
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00793_raw leaf00793_rectangular
    leaf00793_transform leaf00793_sign leaf00793_log
#print axioms leaf00793_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
