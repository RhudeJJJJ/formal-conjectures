/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00254 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 89556030918715176579497984000000000000 85441252804705987095144513284534697984 4296675392443382515416170496000000000000))
theorem leaf00254_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 89556030918715176579497984000000000000 85441252804705987095144513284534697984 4296675392443382515416170496000000000000 raw00254=true := by decide +kernel
#print axioms leaf00254_raw
theorem leaf00254_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00254=true := by decide +kernel
#print axioms leaf00254_rectangular
def affine00254 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00254 (IntegerComputedClassCell.leftNumerator ![(17/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/3200),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00254_transform : affine00254=(NestedInteger.clearedAll 3 raw00254 (IntegerComputedClassCell.leftNumerator ![(17/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/3200),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00254_transform
theorem leaf00254_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00254=true := by decide +kernel
#print axioms leaf00254_sign
theorem leaf00254_log : RationalLog.accepts (2008867287/2147483648) (-143292463/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00254_log
def leaf00254 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (621419797/31250000000) (2008867287/2147483648) (-143292463/4294967296) 1 8 ![60,0,4] ![(17/3200),0,(1/2)] ![(1/6400),1,(1/2)] affine00254
theorem leaf00254_checked : FastNestedCellData.accepts 1 2 4 leaf00254=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (621419797/31250000000) (2008867287/2147483648) (-143292463/4294967296) 1 8 ![60,0,4] ![(17/3200),0,(1/2)] ![(1/6400),1,(1/2)] 89556030918715176579497984000000000000 85441252804705987095144513284534697984 4296675392443382515416170496000000000000 raw00254 affine00254
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00254_raw leaf00254_rectangular
    leaf00254_transform leaf00254_sign leaf00254_log
#print axioms leaf00254_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
