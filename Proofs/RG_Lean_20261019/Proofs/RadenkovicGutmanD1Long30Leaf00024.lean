/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00024 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 872627239097926845125592350720000000000 862594899890906276878723848945046388736 182346672721604051107376529408000000000000))
theorem leaf00024_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 872627239097926845125592350720000000000 862594899890906276878723848945046388736 182346672721604051107376529408000000000000 raw00024=true := by decide +kernel
#print axioms leaf00024_raw
theorem leaf00024_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00024=true := by decide +kernel
#print axioms leaf00024_rectangular
def affine00024 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00024 (IntegerComputedClassCell.leftNumerator ![(1/800),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/800),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/800),0,(1/2)] ![(1/16000),1,(1/2)]))
theorem leaf00024_transform : affine00024=(NestedInteger.clearedAll 3 raw00024 (IntegerComputedClassCell.leftNumerator ![(1/800),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/800),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/800),0,(1/2)] ![(1/16000),1,(1/2)])) := by decide +kernel
#print axioms leaf00024_transform
theorem leaf00024_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00024=true := by decide +kernel
#print axioms leaf00024_sign
theorem leaf00024_log : RationalLog.accepts (4225600025/4294967296) (-17483405/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00024_log
def leaf00024 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (2365260871/500000000000) (4225600025/4294967296) (-17483405/2147483648) 1 8 ![60,0,4] ![(1/800),0,(1/2)] ![(1/16000),1,(1/2)] affine00024
theorem leaf00024_checked : FastNestedCellData.accepts 1 2 4 leaf00024=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (2365260871/500000000000) (4225600025/4294967296) (-17483405/2147483648) 1 8 ![60,0,4] ![(1/800),0,(1/2)] ![(1/16000),1,(1/2)] 872627239097926845125592350720000000000 862594899890906276878723848945046388736 182346672721604051107376529408000000000000 raw00024 affine00024
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00024_raw leaf00024_rectangular
    leaf00024_transform leaf00024_sign leaf00024_log
#print axioms leaf00024_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
