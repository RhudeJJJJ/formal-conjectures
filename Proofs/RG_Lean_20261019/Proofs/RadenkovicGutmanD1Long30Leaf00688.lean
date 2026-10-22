/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00688 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 229387351388631440405926248448000000000000 151900643945727706036909323821895997456384 763466328498428445183503761408000000000000))
theorem leaf00688_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 229387351388631440405926248448000000000000 151900643945727706036909323821895997456384 763466328498428445183503761408000000000000 raw00688=true := by decide +kernel
#print axioms leaf00688_raw
theorem leaf00688_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00688=true := by decide +kernel
#print axioms leaf00688_rectangular
def affine00688 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00688 (IntegerComputedClassCell.leftNumerator ![(11/400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/400),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00688_transform : affine00688=(NestedInteger.clearedAll 3 raw00688 (IntegerComputedClassCell.leftNumerator ![(11/400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/400),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00688_transform
theorem leaf00688_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00688=true := by decide +kernel
#print axioms leaf00688_sign
theorem leaf00688_log : RationalLog.accepts (593040929/1073741824) (-1274835325/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00688_log
def leaf00688 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (198961811773/1000000000000) (593040929/1073741824) (-1274835325/4294967296) 1 8 ![60,0,4] ![(11/400),0,(1/4)] ![(3/6400),1,(1/4)] affine00688
theorem leaf00688_checked : FastNestedCellData.accepts 1 2 4 leaf00688=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (198961811773/1000000000000) (593040929/1073741824) (-1274835325/4294967296) 1 8 ![60,0,4] ![(11/400),0,(1/4)] ![(3/6400),1,(1/4)] 229387351388631440405926248448000000000000 151900643945727706036909323821895997456384 763466328498428445183503761408000000000000 raw00688 affine00688
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00688_raw leaf00688_rectangular
    leaf00688_transform leaf00688_sign leaf00688_log
#print axioms leaf00688_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
