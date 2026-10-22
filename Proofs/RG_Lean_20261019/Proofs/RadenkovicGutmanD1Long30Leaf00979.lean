/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00979 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 479033517281523305527591829504000000000000 322023409969960672288876524665391827386368 1033379922830477536576516653056000000000000))
theorem leaf00979_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 479033517281523305527591829504000000000000 322023409969960672288876524665391827386368 1033379922830477536576516653056000000000000 raw00979=true := by decide +kernel
#print axioms leaf00979_raw
theorem leaf00979_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00979=true := by decide +kernel
#print axioms leaf00979_rectangular
def affine00979 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00979 (IntegerComputedClassCell.leftNumerator ![(19/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/160),0,(1/2)] ![(1/160),1,(1/2)]))
theorem leaf00979_transform : affine00979=(NestedInteger.clearedAll 3 raw00979 (IntegerComputedClassCell.leftNumerator ![(19/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/160),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/160),0,(1/2)] ![(1/160),1,(1/2)])) := by decide +kernel
#print axioms leaf00979_transform
theorem leaf00979_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00979=true := by decide +kernel
#print axioms leaf00979_sign
theorem leaf00979_log : RationalLog.accepts (2201267769/4294967296) (-1435400629/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00979_log
def leaf00979 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (155810754039/500000000000) (2201267769/4294967296) (-1435400629/4294967296) 1 8 ![60,0,4] ![(19/160),0,(1/2)] ![(1/160),1,(1/2)] affine00979
theorem leaf00979_checked : FastNestedCellData.accepts 1 2 4 leaf00979=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (155810754039/500000000000) (2201267769/4294967296) (-1435400629/4294967296) 1 8 ![60,0,4] ![(19/160),0,(1/2)] ![(1/160),1,(1/2)] 479033517281523305527591829504000000000000 322023409969960672288876524665391827386368 1033379922830477536576516653056000000000000 raw00979 affine00979
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00979_raw leaf00979_rectangular
    leaf00979_transform leaf00979_sign leaf00979_log
#print axioms leaf00979_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
