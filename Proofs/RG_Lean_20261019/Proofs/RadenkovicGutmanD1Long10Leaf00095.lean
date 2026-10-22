/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00095 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 27175378961338432937982846566400000000000 24914521347477410744457136123290291535872 676482634769856947050184389427200000000000))
theorem leaf00095_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 27175378961338432937982846566400000000000 24914521347477410744457136123290291535872 676482634769856947050184389427200000000000 raw00095=true := by decide +kernel
#print axioms leaf00095_raw
theorem leaf00095_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00095=true := by decide +kernel
#print axioms leaf00095_rectangular
def affine00095 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00095 (IntegerComputedClassCell.leftNumerator ![(1/100),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/100),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/100),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00095_transform : affine00095=(NestedInteger.clearedAll 3 raw00095 (IntegerComputedClassCell.leftNumerator ![(1/100),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/100),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/100),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00095_transform
theorem leaf00095_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00095=true := by decide +kernel
#print axioms leaf00095_sign
theorem leaf00095_log : RationalLog.accepts (3797776933/4294967296) (-132100395/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00095_log
def leaf00095 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (7365901227/200000000000) (3797776933/4294967296) (-132100395/2147483648) 1 8 ![52,0,4] ![(1/100),0,(1/2)] ![(1/3200),1,(1/2)] affine00095
theorem leaf00095_checked : FastNestedCellData.accepts 1 0 4 leaf00095=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (7365901227/200000000000) (3797776933/4294967296) (-132100395/2147483648) 1 8 ![52,0,4] ![(1/100),0,(1/2)] ![(1/3200),1,(1/2)] 27175378961338432937982846566400000000000 24914521347477410744457136123290291535872 676482634769856947050184389427200000000000 raw00095 affine00095
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00095_raw leaf00095_rectangular
    leaf00095_transform leaf00095_sign leaf00095_log
#print axioms leaf00095_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
