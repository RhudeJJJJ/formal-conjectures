/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00755 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1802591541372445999821653803008000000000000 77450511860098434306164466362739874332672 88065169745878445689369788416000000000000))
theorem leaf00755_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1802591541372445999821653803008000000000000 77450511860098434306164466362739874332672 88065169745878445689369788416000000000000 raw00755=true := by decide +kernel
#print axioms leaf00755_raw
theorem leaf00755_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00755=true := by decide +kernel
#print axioms leaf00755_rectangular
def affine00755 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00755 (IntegerComputedClassCell.leftNumerator ![(109/3200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(109/3200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(109/3200),0,0] ![(3/3200),1,(1/16)]))
theorem leaf00755_transform : affine00755=(NestedInteger.clearedAll 3 raw00755 (IntegerComputedClassCell.leftNumerator ![(109/3200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(109/3200),0,0] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(109/3200),0,0] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00755_transform
theorem leaf00755_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00755=true := by decide +kernel
#print axioms leaf00755_sign
theorem leaf00755_log : RationalLog.accepts (98186517/4294967296) (-8113902781/4294967296) 6 8=true := by decide +kernel
#print axioms leaf00755_log
def leaf00755 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (879468149367/1000000000000) (98186517/4294967296) (-8113902781/4294967296) 6 8 ![60,0,4] ![(109/3200),0,0] ![(3/3200),1,(1/16)] affine00755
theorem leaf00755_checked : FastNestedCellData.accepts 1 2 4 leaf00755=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (879468149367/1000000000000) (98186517/4294967296) (-8113902781/4294967296) 6 8 ![60,0,4] ![(109/3200),0,0] ![(3/3200),1,(1/16)] 1802591541372445999821653803008000000000000 77450511860098434306164466362739874332672 88065169745878445689369788416000000000000 raw00755 affine00755
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00755_raw leaf00755_rectangular
    leaf00755_transform leaf00755_sign leaf00755_log
#print axioms leaf00755_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
