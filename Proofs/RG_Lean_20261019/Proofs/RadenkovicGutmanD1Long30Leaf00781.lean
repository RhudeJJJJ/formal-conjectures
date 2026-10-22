/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00781 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2504786592273968441384537738444800000000000 631307544668955131013418907939686135627776 929865142541964515565197328384000000000000))
theorem leaf00781_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2504786592273968441384537738444800000000000 631307544668955131013418907939686135627776 929865142541964515565197328384000000000000 raw00781=true := by decide +kernel
#print axioms leaf00781_raw
theorem leaf00781_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00781=true := by decide +kernel
#print axioms leaf00781_rectangular
def affine00781 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00781 (IntegerComputedClassCell.leftNumerator ![(31/800),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/800),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/800),0,(1/16)] ![(3/3200),1,(1/16)]))
theorem leaf00781_transform : affine00781=(NestedInteger.clearedAll 3 raw00781 (IntegerComputedClassCell.leftNumerator ![(31/800),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/800),0,(1/16)] ![(3/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/800),0,(1/16)] ![(3/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00781_transform
theorem leaf00781_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00781=true := by decide +kernel
#print axioms leaf00781_sign
theorem leaf00781_log : RationalLog.accepts (644761555/4294967296) (-2036156703/2147483648) 3 8=true := by decide +kernel
#print axioms leaf00781_log
def leaf00781 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (678923766239/1000000000000) (644761555/4294967296) (-2036156703/2147483648) 3 8 ![60,0,4] ![(31/800),0,(1/16)] ![(3/3200),1,(1/16)] affine00781
theorem leaf00781_checked : FastNestedCellData.accepts 1 2 4 leaf00781=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (678923766239/1000000000000) (644761555/4294967296) (-2036156703/2147483648) 3 8 ![60,0,4] ![(31/800),0,(1/16)] ![(3/3200),1,(1/16)] 2504786592273968441384537738444800000000000 631307544668955131013418907939686135627776 929865142541964515565197328384000000000000 raw00781 affine00781
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00781_raw leaf00781_rectangular
    leaf00781_transform leaf00781_sign leaf00781_log
#print axioms leaf00781_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
