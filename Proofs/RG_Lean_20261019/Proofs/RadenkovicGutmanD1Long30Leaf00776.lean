/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00776 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3110222367203460324716600885248000000000000 786584266009003572045262672391975097860096 1166308782330029932714926276608000000000000))
theorem leaf00776_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3110222367203460324716600885248000000000000 786584266009003572045262672391975097860096 1166308782330029932714926276608000000000000 raw00776=true := by decide +kernel
#print axioms leaf00776_raw
theorem leaf00776_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00776=true := by decide +kernel
#print axioms leaf00776_rectangular
def affine00776 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00776 (IntegerComputedClassCell.leftNumerator ![(121/3200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(121/3200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(121/3200),0,(1/16)] ![(3/3200),1,(1/16)]))
theorem leaf00776_transform : affine00776=(NestedInteger.clearedAll 3 raw00776 (IntegerComputedClassCell.leftNumerator ![(121/3200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(121/3200),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(121/3200),0,(1/16)] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00776_transform
theorem leaf00776_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00776=true := by decide +kernel
#print axioms leaf00776_sign
theorem leaf00776_log : RationalLog.accepts (324353633/2147483648) (-1014802905/1073741824) 3 8=true := by decide +kernel
#print axioms leaf00776_log
def leaf00776 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (674421969487/1000000000000) (324353633/2147483648) (-1014802905/1073741824) 3 8 ![60,0,4] ![(121/3200),0,(1/16)] ![(3/3200),1,(1/16)] affine00776
theorem leaf00776_checked : FastNestedCellData.accepts 1 2 4 leaf00776=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (674421969487/1000000000000) (324353633/2147483648) (-1014802905/1073741824) 3 8 ![60,0,4] ![(121/3200),0,(1/16)] ![(3/3200),1,(1/16)] 3110222367203460324716600885248000000000000 786584266009003572045262672391975097860096 1166308782330029932714926276608000000000000 raw00776 affine00776
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00776_raw leaf00776_rectangular
    leaf00776_transform leaf00776_sign leaf00776_log
#print axioms leaf00776_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
