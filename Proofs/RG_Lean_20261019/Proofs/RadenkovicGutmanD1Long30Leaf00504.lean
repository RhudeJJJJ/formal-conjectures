/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00504 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 230117500164237757427727990784000000000000 205335966334254689152052266486504257224704 4115049939044673260352044007424000000000000))
theorem leaf00504_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 230117500164237757427727990784000000000000 205335966334254689152052266486504257224704 4115049939044673260352044007424000000000000 raw00504=true := by decide +kernel
#print axioms leaf00504_raw
theorem leaf00504_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00504=true := by decide +kernel
#print axioms leaf00504_rectangular
def affine00504 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00504 (IntegerComputedClassCell.leftNumerator ![(43/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(43/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(43/3200),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00504_transform : affine00504=(NestedInteger.clearedAll 3 raw00504 (IntegerComputedClassCell.leftNumerator ![(43/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(43/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(43/3200),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00504_transform
theorem leaf00504_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00504=true := by decide +kernel
#print axioms leaf00504_sign
theorem leaf00504_log : RationalLog.accepts (1825146853/2147483648) (-174629425/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00504_log
def leaf00504 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (49898778721/1000000000000) (1825146853/2147483648) (-174629425/2147483648) 1 8 ![60,0,4] ![(43/3200),0,(1/2)] ![(1/3200),1,(1/2)] affine00504
theorem leaf00504_checked : FastNestedCellData.accepts 1 2 4 leaf00504=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (49898778721/1000000000000) (1825146853/2147483648) (-174629425/2147483648) 1 8 ![60,0,4] ![(43/3200),0,(1/2)] ![(1/3200),1,(1/2)] 230117500164237757427727990784000000000000 205335966334254689152052266486504257224704 4115049939044673260352044007424000000000000 raw00504 affine00504
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00504_raw leaf00504_rectangular
    leaf00504_transform leaf00504_sign leaf00504_log
#print axioms leaf00504_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
