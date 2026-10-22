/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00804 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2765678921843416691111433863168000000000000 2047256311212728413193489805233963145363456 13654952108850042754941868572672000000000000))
theorem leaf00804_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2765678921843416691111433863168000000000000 2047256311212728413193489805233963145363456 13654952108850042754941868572672000000000000 raw00804=true := by decide +kernel
#print axioms leaf00804_raw
theorem leaf00804_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00804=true := by decide +kernel
#print axioms leaf00804_rectangular
def affine00804 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00804 (IntegerComputedClassCell.leftNumerator ![(17/400),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/400),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/400),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00804_transform : affine00804=(NestedInteger.clearedAll 3 raw00804 (IntegerComputedClassCell.leftNumerator ![(17/400),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/400),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/400),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00804_transform
theorem leaf00804_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00804=true := by decide +kernel
#print axioms leaf00804_sign
theorem leaf00804_log : RationalLog.accepts (2764774809/4294967296) (-945933839/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00804_log
def leaf00804 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (149927754773/1000000000000) (2764774809/4294967296) (-945933839/4294967296) 1 8 ![60,0,4] ![(17/400),0,(1/2)] ![(3/3200),1,(1/2)] affine00804
theorem leaf00804_checked : FastNestedCellData.accepts 1 2 4 leaf00804=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (149927754773/1000000000000) (2764774809/4294967296) (-945933839/4294967296) 1 8 ![60,0,4] ![(17/400),0,(1/2)] ![(3/3200),1,(1/2)] 2765678921843416691111433863168000000000000 2047256311212728413193489805233963145363456 13654952108850042754941868572672000000000000 raw00804 affine00804
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00804_raw leaf00804_rectangular
    leaf00804_transform leaf00804_sign leaf00804_log
#print axioms leaf00804_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
