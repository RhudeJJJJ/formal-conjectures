/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00138 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2289728833478417435481318883328000000000000 12147325513668500418120953340331277942784 32620835802971276293298978816000000000000))
theorem leaf00138_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2289728833478417435481318883328000000000000 12147325513668500418120953340331277942784 32620835802971276293298978816000000000000 raw00138=true := by decide +kernel
#print axioms leaf00138_raw
theorem leaf00138_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00138=true := by decide +kernel
#print axioms leaf00138_rectangular
def affine00138 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00138 (IntegerComputedClassCell.leftNumerator ![(7/400),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/400),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/400),0,0] ![(1/1600),1,(1/4)]))
theorem leaf00138_transform : affine00138=(NestedInteger.clearedAll 3 raw00138 (IntegerComputedClassCell.leftNumerator ![(7/400),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/400),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/400),0,0] ![(1/1600),1,(1/4)])) := by decide +kernel
#print axioms leaf00138_transform
theorem leaf00138_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00138=true := by decide +kernel
#print axioms leaf00138_sign
theorem leaf00138_log : RationalLog.accepts (16602837/4294967296) (-5965307763/2147483648) 9 8=true := by decide +kernel
#print axioms leaf00138_log
def leaf00138 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (372379346349/1000000000000) (16602837/4294967296) (-5965307763/2147483648) 9 8 ![52,0,4] ![(7/400),0,0] ![(1/1600),1,(1/4)] affine00138
theorem leaf00138_checked : FastNestedCellData.accepts 1 0 4 leaf00138=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (372379346349/1000000000000) (16602837/4294967296) (-5965307763/2147483648) 9 8 ![52,0,4] ![(7/400),0,0] ![(1/1600),1,(1/4)] 2289728833478417435481318883328000000000000 12147325513668500418120953340331277942784 32620835802971276293298978816000000000000 raw00138 affine00138
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00138_raw leaf00138_rectangular
    leaf00138_transform leaf00138_sign leaf00138_log
#print axioms leaf00138_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
