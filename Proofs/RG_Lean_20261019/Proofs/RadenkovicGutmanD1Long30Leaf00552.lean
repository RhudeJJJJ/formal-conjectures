/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00552 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 176452215570058060121925222400000000000 104428400252212145152587492724769292288 426453090832203600807277363200000000000))
theorem leaf00552_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 176452215570058060121925222400000000000 104428400252212145152587492724769292288 426453090832203600807277363200000000000 raw00552=true := by decide +kernel
#print axioms leaf00552_raw
theorem leaf00552_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00552=true := by decide +kernel
#print axioms leaf00552_rectangular
def affine00552 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00552 (IntegerComputedClassCell.leftNumerator ![(53/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(53/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(53/3200),0,(1/8)] ![(1/3200),1,(1/8)]))
theorem leaf00552_transform : affine00552=(NestedInteger.clearedAll 3 raw00552 (IntegerComputedClassCell.leftNumerator ![(53/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(53/3200),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(53/3200),0,(1/8)] ![(1/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00552_transform
theorem leaf00552_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00552=true := by decide +kernel
#print axioms leaf00552_sign
theorem leaf00552_log : RationalLog.accepts (127615983/268435456) (-798418217/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00552_log
def leaf00552 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (24487664059/100000000000) (127615983/268435456) (-798418217/2147483648) 2 8 ![60,0,4] ![(53/3200),0,(1/8)] ![(1/3200),1,(1/8)] affine00552
theorem leaf00552_checked : FastNestedCellData.accepts 1 2 4 leaf00552=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (24487664059/100000000000) (127615983/268435456) (-798418217/2147483648) 2 8 ![60,0,4] ![(53/3200),0,(1/8)] ![(1/3200),1,(1/8)] 176452215570058060121925222400000000000 104428400252212145152587492724769292288 426453090832203600807277363200000000000 raw00552 affine00552
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00552_raw leaf00552_rectangular
    leaf00552_transform leaf00552_sign leaf00552_log
#print axioms leaf00552_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
