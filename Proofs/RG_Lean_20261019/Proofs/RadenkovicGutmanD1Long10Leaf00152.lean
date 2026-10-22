/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00152 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 67126403026989908752391890534400000000000 56985854456194855761225334079358471503872 783002980624795223100756066304000000000000))
theorem leaf00152_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 67126403026989908752391890534400000000000 56985854456194855761225334079358471503872 783002980624795223100756066304000000000000 raw00152=true := by decide +kernel
#print axioms leaf00152_raw
theorem leaf00152_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00152=true := by decide +kernel
#print axioms leaf00152_rectangular
def affine00152 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00152 (IntegerComputedClassCell.leftNumerator ![(1/50),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/50),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/50),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00152_transform : affine00152=(NestedInteger.clearedAll 3 raw00152 (IntegerComputedClassCell.leftNumerator ![(1/50),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/50),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/50),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00152_transform
theorem leaf00152_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00152=true := by decide +kernel
#print axioms leaf00152_sign
theorem leaf00152_log : RationalLog.accepts (1699391555/2147483648) (-31410505/268435456) 1 8=true := by decide +kernel
#print axioms leaf00152_log
def leaf00152 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (72778591993/1000000000000) (1699391555/2147483648) (-31410505/268435456) 1 8 ![52,0,4] ![(1/50),0,(1/2)] ![(3/6400),1,(1/2)] affine00152
theorem leaf00152_checked : FastNestedCellData.accepts 1 0 4 leaf00152=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (72778591993/1000000000000) (1699391555/2147483648) (-31410505/268435456) 1 8 ![52,0,4] ![(1/50),0,(1/2)] ![(3/6400),1,(1/2)] 67126403026989908752391890534400000000000 56985854456194855761225334079358471503872 783002980624795223100756066304000000000000 raw00152 affine00152
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00152_raw leaf00152_rectangular
    leaf00152_transform leaf00152_sign leaf00152_log
#print axioms leaf00152_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
