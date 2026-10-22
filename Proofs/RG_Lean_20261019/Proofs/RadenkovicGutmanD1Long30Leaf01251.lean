/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01251 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 77327107570540216926932566016000000000000 82962368773563964247590018752598952116224 19791062055677973067584057114624000000000000))
theorem leaf01251_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 77327107570540216926932566016000000000000 82962368773563964247590018752598952116224 19791062055677973067584057114624000000000000 raw01251=true := by decide +kernel
#print axioms leaf01251_raw
theorem leaf01251_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01251=true := by decide +kernel
#print axioms leaf01251_rectangular
def affine01251 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01251 (IntegerComputedClassCell.leftNumerator ![(27/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(27/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(27/128),0,(1/2)] ![(1/128),1,(1/4)]))
theorem leaf01251_transform : affine01251=(NestedInteger.clearedAll 3 raw01251 (IntegerComputedClassCell.leftNumerator ![(27/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(27/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(27/128),0,(1/2)] ![(1/128),1,(1/4)])) := by decide +kernel
#print axioms leaf01251_transform
theorem leaf01251_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01251=true := by decide +kernel
#print axioms leaf01251_sign
theorem leaf01251_log : RationalLog.accepts (4588730169/4294967296) (142076215/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01251_log
def leaf01251 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (4191910901/1000000000000) (4588730169/4294967296) (142076215/4294967296) 0 8 ![60,0,4] ![(27/128),0,(1/2)] ![(1/128),1,(1/4)] affine01251
theorem leaf01251_checked : FastNestedCellData.accepts 1 2 4 leaf01251=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (4191910901/1000000000000) (4588730169/4294967296) (142076215/4294967296) 0 8 ![60,0,4] ![(27/128),0,(1/2)] ![(1/128),1,(1/4)] 77327107570540216926932566016000000000000 82962368773563964247590018752598952116224 19791062055677973067584057114624000000000000 raw01251 affine01251
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01251_raw leaf01251_rectangular
    leaf01251_transform leaf01251_sign leaf01251_log
#print axioms leaf01251_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
