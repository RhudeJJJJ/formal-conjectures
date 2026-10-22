/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00564 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 39003486815615449817847693312000000000 33836119042898494414853769600562102272 533427717529113572223955763200000000000))
theorem leaf00564_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 39003486815615449817847693312000000000 33836119042898494414853769600562102272 533427717529113572223955763200000000000 raw00564=true := by decide +kernel
#print axioms leaf00564_raw
theorem leaf00564_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00564=true := by decide +kernel
#print axioms leaf00564_rectangular
def affine00564 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00564 (IntegerComputedClassCell.leftNumerator ![(11/640),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/640),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/640),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00564_transform : affine00564=(NestedInteger.clearedAll 3 raw00564 (IntegerComputedClassCell.leftNumerator ![(11/640),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/640),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/640),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00564_transform
theorem leaf00564_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00564=true := by decide +kernel
#print axioms leaf00564_sign
theorem leaf00564_log : RationalLog.accepts (1751852175/2147483648) (-437277413/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00564_log
def leaf00564 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (6343149771/100000000000) (1751852175/2147483648) (-437277413/4294967296) 1 8 ![60,0,4] ![(11/640),0,(1/2)] ![(1/3200),1,(1/2)] affine00564
theorem leaf00564_checked : FastNestedCellData.accepts 1 2 4 leaf00564=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (6343149771/100000000000) (1751852175/2147483648) (-437277413/4294967296) 1 8 ![60,0,4] ![(11/640),0,(1/2)] ![(1/3200),1,(1/2)] 39003486815615449817847693312000000000 33836119042898494414853769600562102272 533427717529113572223955763200000000000 raw00564 affine00564
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00564_raw leaf00564_rectangular
    leaf00564_transform leaf00564_sign leaf00564_log
#print axioms leaf00564_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
