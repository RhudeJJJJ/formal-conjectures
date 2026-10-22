/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00947 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 442306549399956569240099828531200000000000 191357705144815696194151157717814411788288 319228970778530852863374629273600000000000))
theorem leaf00947_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 442306549399956569240099828531200000000000 191357705144815696194151157717814411788288 319228970778530852863374629273600000000000 raw00947=true := by decide +kernel
#print axioms leaf00947_raw
theorem leaf00947_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00947=true := by decide +kernel
#print axioms leaf00947_rectangular
def affine00947 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00947 (IntegerComputedClassCell.leftNumerator ![(3/32),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/32),0,(1/8)] ![(1/320),1,(1/8)]))
theorem leaf00947_transform : affine00947=(NestedInteger.clearedAll 3 raw00947 (IntegerComputedClassCell.leftNumerator ![(3/32),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,(1/8)] ![(1/320),1,(1/8)]) (IntegerComputedClassCell.denominator ![(3/32),0,(1/8)] ![(1/320),1,(1/8)])) := by decide +kernel
#print axioms leaf00947_transform
theorem leaf00947_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00947=true := by decide +kernel
#print axioms leaf00947_sign
theorem leaf00947_log : RationalLog.accepts (1161756913/4294967296) (-2807857493/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00947_log
def leaf00947 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (119887430441/200000000000) (1161756913/4294967296) (-2807857493/4294967296) 2 8 ![60,0,4] ![(3/32),0,(1/8)] ![(1/320),1,(1/8)] affine00947
theorem leaf00947_checked : FastNestedCellData.accepts 1 2 4 leaf00947=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (119887430441/200000000000) (1161756913/4294967296) (-2807857493/4294967296) 2 8 ![60,0,4] ![(3/32),0,(1/8)] ![(1/320),1,(1/8)] 442306549399956569240099828531200000000000 191357705144815696194151157717814411788288 319228970778530852863374629273600000000000 raw00947 affine00947
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00947_raw leaf00947_rectangular
    leaf00947_transform leaf00947_sign leaf00947_log
#print axioms leaf00947_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
