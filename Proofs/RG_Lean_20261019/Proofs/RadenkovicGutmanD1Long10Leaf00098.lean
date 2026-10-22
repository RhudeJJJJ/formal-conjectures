/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00098 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 34187865989191764387089612800000000000 31266138645992546436567844963894689792 823743549245936369965989888000000000000))
theorem leaf00098_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 34187865989191764387089612800000000000 31266138645992546436567844963894689792 823743549245936369965989888000000000000 raw00098=true := by decide +kernel
#print axioms leaf00098_raw
theorem leaf00098_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00098=true := by decide +kernel
#print axioms leaf00098_rectangular
def affine00098 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00098 (IntegerComputedClassCell.leftNumerator ![(33/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(33/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(33/3200),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00098_transform : affine00098=(NestedInteger.clearedAll 3 raw00098 (IntegerComputedClassCell.leftNumerator ![(33/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(33/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(33/3200),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00098_transform
theorem leaf00098_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00098=true := by decide +kernel
#print axioms leaf00098_sign
theorem leaf00098_log : RationalLog.accepts (946069665/1073741824) (-135923547/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00098_log
def leaf00098 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (2372259749/62500000000) (946069665/1073741824) (-135923547/2147483648) 1 8 ![52,0,4] ![(33/3200),0,(1/2)] ![(1/3200),1,(1/2)] affine00098
theorem leaf00098_checked : FastNestedCellData.accepts 1 0 4 leaf00098=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (2372259749/62500000000) (946069665/1073741824) (-135923547/2147483648) 1 8 ![52,0,4] ![(33/3200),0,(1/2)] ![(1/3200),1,(1/2)] 34187865989191764387089612800000000000 31266138645992546436567844963894689792 823743549245936369965989888000000000000 raw00098 affine00098
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00098_raw leaf00098_rectangular
    leaf00098_transform leaf00098_sign leaf00098_log
#print axioms leaf00098_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
