/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00675 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 639331512666995206683170019737600000000000 16725003773243997473366383490920523759616 19302778488102246500796884582400000000000))
theorem leaf00675_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 639331512666995206683170019737600000000000 16725003773243997473366383490920523759616 19302778488102246500796884582400000000000 raw00675=true := by decide +kernel
#print axioms leaf00675_raw
theorem leaf00675_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00675=true := by decide +kernel
#print axioms leaf00675_rectangular
def affine00675 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00675 (IntegerComputedClassCell.leftNumerator ![(17/640),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/640),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/640),0,0] ![(3/6400),1,(1/16)]))
theorem leaf00675_transform : affine00675=(NestedInteger.clearedAll 3 raw00675 (IntegerComputedClassCell.leftNumerator ![(17/640),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/640),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/640),0,0] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00675_transform
theorem leaf00675_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00675=true := by decide +kernel
#print axioms leaf00675_sign
theorem leaf00675_log : RationalLog.accepts (60198029/4294967296) (-9164514725/4294967296) 7 8=true := by decide +kernel
#print axioms leaf00675_log
def leaf00675 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (173291153743/200000000000) (60198029/4294967296) (-9164514725/4294967296) 7 8 ![60,0,4] ![(17/640),0,0] ![(3/6400),1,(1/16)] affine00675
theorem leaf00675_checked : FastNestedCellData.accepts 1 2 4 leaf00675=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (173291153743/200000000000) (60198029/4294967296) (-9164514725/4294967296) 7 8 ![60,0,4] ![(17/640),0,0] ![(3/6400),1,(1/16)] 639331512666995206683170019737600000000000 16725003773243997473366383490920523759616 19302778488102246500796884582400000000000 raw00675 affine00675
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00675_raw leaf00675_rectangular
    leaf00675_transform leaf00675_sign leaf00675_log
#print axioms leaf00675_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
