/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00004 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 192207867193501829865767174144000000000000 186787114925399469327630849595215597010944 17926498824455542559043345186816000000000000))
theorem leaf00004_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 192207867193501829865767174144000000000000 186787114925399469327630849595215597010944 17926498824455542559043345186816000000000000 raw00004=true := by decide +kernel
#print axioms leaf00004_raw
theorem leaf00004_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00004=true := by decide +kernel
#print axioms leaf00004_rectangular
def affine00004 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00004 (IntegerComputedClassCell.leftNumerator ![(1/800),0,(1/4)] ![(1/4000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/800),0,(1/4)] ![(1/4000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/800),0,(1/4)] ![(1/4000),1,(1/4)]))
theorem leaf00004_transform : affine00004=(NestedInteger.clearedAll 3 raw00004 (IntegerComputedClassCell.leftNumerator ![(1/800),0,(1/4)] ![(1/4000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/800),0,(1/4)] ![(1/4000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/800),0,(1/4)] ![(1/4000),1,(1/4)])) := by decide +kernel
#print axioms leaf00004_transform
theorem leaf00004_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00004=true := by decide +kernel
#print axioms leaf00004_sign
theorem leaf00004_log : RationalLog.accepts (4130796969/4294967296) (-41847583/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00004_log
def leaf00004 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (10419609359/1000000000000) (4130796969/4294967296) (-41847583/2147483648) 1 8 ![52,0,4] ![(1/800),0,(1/4)] ![(1/4000),1,(1/4)] affine00004
theorem leaf00004_checked : FastNestedCellData.accepts 1 0 4 leaf00004=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (10419609359/1000000000000) (4130796969/4294967296) (-41847583/2147483648) 1 8 ![52,0,4] ![(1/800),0,(1/4)] ![(1/4000),1,(1/4)] 192207867193501829865767174144000000000000 186787114925399469327630849595215597010944 17926498824455542559043345186816000000000000 raw00004 affine00004
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00004_raw leaf00004_rectangular
    leaf00004_transform leaf00004_sign leaf00004_log
#print axioms leaf00004_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
