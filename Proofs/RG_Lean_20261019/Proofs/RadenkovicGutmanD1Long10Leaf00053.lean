/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00053 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 24215747227578093569994391552000000000000 23000887310389048474036120169317486559232 1095081533349754101659458338816000000000000))
theorem leaf00053_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 24215747227578093569994391552000000000000 23000887310389048474036120169317486559232 1095081533349754101659458338816000000000000 raw00053=true := by decide +kernel
#print axioms leaf00053_raw
theorem leaf00053_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00053=true := by decide +kernel
#print axioms leaf00053_rectangular
def affine00053 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00053 (IntegerComputedClassCell.leftNumerator ![(9/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/1600),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00053_transform : affine00053=(NestedInteger.clearedAll 3 raw00053 (IntegerComputedClassCell.leftNumerator ![(9/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/1600),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00053_transform
theorem leaf00053_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00053=true := by decide +kernel
#print axioms leaf00053_sign
theorem leaf00053_log : RationalLog.accepts (1997787159/2147483648) (-155169931/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00053_log
def leaf00053 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (10501906301/500000000000) (1997787159/2147483648) (-155169931/4294967296) 1 8 ![52,0,4] ![(9/1600),0,(1/2)] ![(1/3200),1,(1/2)] affine00053
theorem leaf00053_checked : FastNestedCellData.accepts 1 0 4 leaf00053=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (10501906301/500000000000) (1997787159/2147483648) (-155169931/4294967296) 1 8 ![52,0,4] ![(9/1600),0,(1/2)] ![(1/3200),1,(1/2)] 24215747227578093569994391552000000000000 23000887310389048474036120169317486559232 1095081533349754101659458338816000000000000 raw00053 affine00053
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00053_raw leaf00053_rectangular
    leaf00053_transform leaf00053_sign leaf00053_log
#print axioms leaf00053_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
