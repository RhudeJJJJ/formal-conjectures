/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01034 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 6341490422232043159742488510464000000000000 5031414160715321623434138446998123824807936 14635866834422465340757963177984000000000000))
theorem leaf01034_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 6341490422232043159742488510464000000000000 5031414160715321623434138446998123824807936 14635866834422465340757963177984000000000000 raw01034=true := by decide +kernel
#print axioms leaf01034_raw
theorem leaf01034_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01034=true := by decide +kernel
#print axioms leaf01034_rectangular
def affine01034 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01034 (IntegerComputedClassCell.leftNumerator ![(67/320),0,(1/2)] ![(3/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(67/320),0,(1/2)] ![(3/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(67/320),0,(1/2)] ![(3/320),1,(1/2)]))
theorem leaf01034_transform : affine01034=(NestedInteger.clearedAll 3 raw01034 (IntegerComputedClassCell.leftNumerator ![(67/320),0,(1/2)] ![(3/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(67/320),0,(1/2)] ![(3/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(67/320),0,(1/2)] ![(3/320),1,(1/2)])) := by decide +kernel
#print axioms leaf01034_transform
theorem leaf01034_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01034=true := by decide +kernel
#print axioms leaf01034_sign
theorem leaf01034_log : RationalLog.accepts (2535903451/4294967296) (-565748117/2147483648) 1 8=true := by decide +kernel
#print axioms leaf01034_log
def leaf01034 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (343772884629/1000000000000) (2535903451/4294967296) (-565748117/2147483648) 1 8 ![60,0,4] ![(67/320),0,(1/2)] ![(3/320),1,(1/2)] affine01034
theorem leaf01034_checked : FastNestedCellData.accepts 1 2 4 leaf01034=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (343772884629/1000000000000) (2535903451/4294967296) (-565748117/2147483648) 1 8 ![60,0,4] ![(67/320),0,(1/2)] ![(3/320),1,(1/2)] 6341490422232043159742488510464000000000000 5031414160715321623434138446998123824807936 14635866834422465340757963177984000000000000 raw01034 affine01034
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01034_raw leaf01034_rectangular
    leaf01034_transform leaf01034_sign leaf01034_log
#print axioms leaf01034_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
