/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00150 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 75730567824607229740221412147200000000000 562303573013062422997250485201045291008 1369680751255903104456353382400000000000))
theorem leaf00150_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 75730567824607229740221412147200000000000 562303573013062422997250485201045291008 1369680751255903104456353382400000000000 raw00150=true := by decide +kernel
#print axioms leaf00150_raw
theorem leaf00150_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00150=true := by decide +kernel
#print axioms leaf00150_rectangular
def affine00150 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00150 (IntegerComputedClassCell.leftNumerator ![(1/50),0,0] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/50),0,0] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/50),0,0] ![(3/6400),1,(1/4)]))
theorem leaf00150_transform : affine00150=(NestedInteger.clearedAll 3 raw00150 (IntegerComputedClassCell.leftNumerator ![(1/50),0,0] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/50),0,0] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/50),0,0] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00150_transform
theorem leaf00150_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00150=true := by decide +kernel
#print axioms leaf00150_sign
theorem leaf00150_log : RationalLog.accepts (11304341/2147483648) (-11267557563/4294967296) 8 8=true := by decide +kernel
#print axioms leaf00150_log
def leaf00150 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (82107246159/200000000000) (11304341/2147483648) (-11267557563/4294967296) 8 8 ![52,0,4] ![(1/50),0,0] ![(3/6400),1,(1/4)] affine00150
theorem leaf00150_checked : FastNestedCellData.accepts 1 0 4 leaf00150=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (82107246159/200000000000) (11304341/2147483648) (-11267557563/4294967296) 8 8 ![52,0,4] ![(1/50),0,0] ![(3/6400),1,(1/4)] 75730567824607229740221412147200000000000 562303573013062422997250485201045291008 1369680751255903104456353382400000000000 raw00150 affine00150
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00150_raw leaf00150_rectangular
    leaf00150_transform leaf00150_sign leaf00150_log
#print axioms leaf00150_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
