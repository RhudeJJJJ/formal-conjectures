/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00209 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 4795373980464433776987996160000000000 3685770387834471891418466711689494528 29538217168524326280217231360000000000))
theorem leaf00209_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 4795373980464433776987996160000000000 3685770387834471891418466711689494528 29538217168524326280217231360000000000 raw00209=true := by decide +kernel
#print axioms leaf00209_raw
theorem leaf00209_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00209=true := by decide +kernel
#print axioms leaf00209_rectangular
def affine00209 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00209 (IntegerComputedClassCell.leftNumerator ![(7/200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/200),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00209_transform : affine00209=(NestedInteger.clearedAll 3 raw00209 (IntegerComputedClassCell.leftNumerator ![(7/200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/200),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00209_transform
theorem leaf00209_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00209=true := by decide +kernel
#print axioms leaf00209_sign
theorem leaf00209_log : RationalLog.accepts (733733229/1073741824) (-408837251/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00209_log
def leaf00209 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (1247797173/10000000000) (733733229/1073741824) (-408837251/2147483648) 1 8 ![52,0,4] ![(7/200),0,(1/2)] ![(3/3200),1,(1/2)] affine00209
theorem leaf00209_checked : FastNestedCellData.accepts 1 0 4 leaf00209=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (1247797173/10000000000) (733733229/1073741824) (-408837251/2147483648) 1 8 ![52,0,4] ![(7/200),0,(1/2)] ![(3/3200),1,(1/2)] 4795373980464433776987996160000000000 3685770387834471891418466711689494528 29538217168524326280217231360000000000 raw00209 affine00209
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00209_raw leaf00209_rectangular
    leaf00209_transform leaf00209_sign leaf00209_log
#print axioms leaf00209_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
