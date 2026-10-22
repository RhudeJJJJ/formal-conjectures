/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00194 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 69935832097785027699174014976000000000000 67475669651531610249504773765501754015744 4449458782171964352050784894976000000000000))
theorem leaf00194_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 69935832097785027699174014976000000000000 67475669651531610249504773765501754015744 4449458782171964352050784894976000000000000 raw00194=true := by decide +kernel
#print axioms leaf00194_raw
theorem leaf00194_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00194=true := by decide +kernel
#print axioms leaf00194_rectangular
def affine00194 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00194 (IntegerComputedClassCell.leftNumerator ![(13/3200),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/3200),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/3200),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00194_transform : affine00194=(NestedInteger.clearedAll 3 raw00194 (IntegerComputedClassCell.leftNumerator ![(13/3200),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/3200),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/3200),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00194_transform
theorem leaf00194_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00194=true := by decide +kernel
#print axioms leaf00194_sign
theorem leaf00194_log : RationalLog.accepts (2040989273/2147483648) (-54612817/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00194_log
def leaf00194 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (15164916219/1000000000000) (2040989273/2147483648) (-54612817/2147483648) 1 8 ![60,0,4] ![(13/3200),0,(1/2)] ![(3/32000),1,(1/2)] affine00194
theorem leaf00194_checked : FastNestedCellData.accepts 1 2 4 leaf00194=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (15164916219/1000000000000) (2040989273/2147483648) (-54612817/2147483648) 1 8 ![60,0,4] ![(13/3200),0,(1/2)] ![(3/32000),1,(1/2)] 69935832097785027699174014976000000000000 67475669651531610249504773765501754015744 4449458782171964352050784894976000000000000 raw00194 affine00194
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00194_raw leaf00194_rectangular
    leaf00194_transform leaf00194_sign leaf00194_log
#print axioms leaf00194_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
