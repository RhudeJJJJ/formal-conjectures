/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00451 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 19121205003190650486342549504000000000000 20483864711308696700736768592050898599936 4940334695263065155320504385536000000000000))
theorem leaf00451_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 19121205003190650486342549504000000000000 20483864711308696700736768592050898599936 4940334695263065155320504385536000000000000 raw00451=true := by decide +kernel
#print axioms leaf00451_raw
theorem leaf00451_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00451=true := by decide +kernel
#print axioms leaf00451_rectangular
def affine00451 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00451 (IntegerComputedClassCell.leftNumerator ![(13/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/64),0,(1/2)] ![(1/64),1,(1/4)]))
theorem leaf00451_transform : affine00451=(NestedInteger.clearedAll 3 raw00451 (IntegerComputedClassCell.leftNumerator ![(13/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/64),0,(1/2)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf00451_transform
theorem leaf00451_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00451=true := by decide +kernel
#print axioms leaf00451_sign
theorem leaf00451_log : RationalLog.accepts (2291023457/2147483648) (138946233/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00451_log
def leaf00451 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (4146250401/1000000000000) (2291023457/2147483648) (138946233/4294967296) 0 8 ![52,0,4] ![(13/64),0,(1/2)] ![(1/64),1,(1/4)] affine00451
theorem leaf00451_checked : FastNestedCellData.accepts 1 0 4 leaf00451=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (4146250401/1000000000000) (2291023457/2147483648) (138946233/4294967296) 0 8 ![52,0,4] ![(13/64),0,(1/2)] ![(1/64),1,(1/4)] 19121205003190650486342549504000000000000 20483864711308696700736768592050898599936 4940334695263065155320504385536000000000000 raw00451 affine00451
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00451_raw leaf00451_rectangular
    leaf00451_transform leaf00451_sign leaf00451_log
#print axioms leaf00451_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
