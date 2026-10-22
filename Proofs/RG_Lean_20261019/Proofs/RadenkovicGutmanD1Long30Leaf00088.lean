/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00088 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 18796526054758911935179128832000000000000 18077171929722177236537045113838306852864 1108798519446378097828589207552000000000000))
theorem leaf00088_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 18796526054758911935179128832000000000000 18077171929722177236537045113838306852864 1108798519446378097828589207552000000000000 raw00088=true := by decide +kernel
#print axioms leaf00088_raw
theorem leaf00088_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00088=true := by decide +kernel
#print axioms leaf00088_rectangular
def affine00088 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00088 (IntegerComputedClassCell.leftNumerator ![(67/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(67/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(67/32000),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00088_transform : affine00088=(NestedInteger.clearedAll 3 raw00088 (IntegerComputedClassCell.leftNumerator ![(67/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(67/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(67/32000),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00088_transform
theorem leaf00088_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00088=true := by decide +kernel
#print axioms leaf00088_sign
theorem leaf00088_log : RationalLog.accepts (1016083489/1073741824) (-118528377/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00088_log
def leaf00088 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (16303387507/1000000000000) (1016083489/1073741824) (-118528377/4294967296) 1 8 ![60,0,4] ![(67/32000),0,(1/4)] ![(3/32000),1,(1/4)] affine00088
theorem leaf00088_checked : FastNestedCellData.accepts 1 2 4 leaf00088=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (16303387507/1000000000000) (1016083489/1073741824) (-118528377/4294967296) 1 8 ![60,0,4] ![(67/32000),0,(1/4)] ![(3/32000),1,(1/4)] 18796526054758911935179128832000000000000 18077171929722177236537045113838306852864 1108798519446378097828589207552000000000000 raw00088 affine00088
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00088_raw leaf00088_rectangular
    leaf00088_transform leaf00088_sign leaf00088_log
#print axioms leaf00088_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
