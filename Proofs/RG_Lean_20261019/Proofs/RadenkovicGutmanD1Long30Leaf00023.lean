/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00023 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2813298111534433720600625152000000000000 2747792401185151941412787239382614540288 281519130209929697296107175936000000000000))
theorem leaf00023_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2813298111534433720600625152000000000000 2747792401185151941412787239382614540288 281519130209929697296107175936000000000000 raw00023=true := by decide +kernel
#print axioms leaf00023_raw
theorem leaf00023_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00023=true := by decide +kernel
#print axioms leaf00023_rectangular
def affine00023 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00023 (IntegerComputedClassCell.leftNumerator ![(1/800),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/800),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/800),0,(1/4)] ![(1/16000),1,(1/4)]))
theorem leaf00023_transform : affine00023=(NestedInteger.clearedAll 3 raw00023 (IntegerComputedClassCell.leftNumerator ![(1/800),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/800),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/800),0,(1/4)] ![(1/16000),1,(1/4)])) := by decide +kernel
#print axioms leaf00023_transform
theorem leaf00023_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00023=true := by decide +kernel
#print axioms leaf00023_sign
theorem leaf00023_log : RationalLog.accepts (1038603107/1073741824) (-71453123/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00023_log
def leaf00023 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (4880294279/500000000000) (1038603107/1073741824) (-71453123/4294967296) 1 8 ![60,0,4] ![(1/800),0,(1/4)] ![(1/16000),1,(1/4)] affine00023
theorem leaf00023_checked : FastNestedCellData.accepts 1 2 4 leaf00023=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (4880294279/500000000000) (1038603107/1073741824) (-71453123/4294967296) 1 8 ![60,0,4] ![(1/800),0,(1/4)] ![(1/16000),1,(1/4)] 2813298111534433720600625152000000000000 2747792401185151941412787239382614540288 281519130209929697296107175936000000000000 raw00023 affine00023
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00023_raw leaf00023_rectangular
    leaf00023_transform leaf00023_sign leaf00023_log
#print axioms leaf00023_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
