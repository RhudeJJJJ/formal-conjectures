/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00146 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 5891718152395976488681629286400000000000 4665846302994614224877981022565217337344 45651831950966890151593115648000000000000))
theorem leaf00146_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 5891718152395976488681629286400000000000 4665846302994614224877981022565217337344 45651831950966890151593115648000000000000 raw00146=true := by decide +kernel
#print axioms leaf00146_raw
theorem leaf00146_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00146=true := by decide +kernel
#print axioms leaf00146_rectangular
def affine00146 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00146 (IntegerComputedClassCell.leftNumerator ![(103/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(103/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(103/32000),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00146_transform : affine00146=(NestedInteger.clearedAll 3 raw00146 (IntegerComputedClassCell.leftNumerator ![(103/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(103/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(103/32000),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00146_transform
theorem leaf00146_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00146=true := by decide +kernel
#print axioms leaf00146_sign
theorem leaf00146_log : RationalLog.accepts (3085929095/4294967296) (-354969577/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00146_log
def leaf00146 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (12775627241/125000000000) (3085929095/4294967296) (-354969577/2147483648) 1 8 ![60,0,4] ![(103/32000),0,(1/16)] ![(3/32000),1,(1/16)] affine00146
theorem leaf00146_checked : FastNestedCellData.accepts 1 2 4 leaf00146=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (12775627241/125000000000) (3085929095/4294967296) (-354969577/2147483648) 1 8 ![60,0,4] ![(103/32000),0,(1/16)] ![(3/32000),1,(1/16)] 5891718152395976488681629286400000000000 4665846302994614224877981022565217337344 45651831950966890151593115648000000000000 raw00146 affine00146
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00146_raw leaf00146_rectangular
    leaf00146_transform leaf00146_sign leaf00146_log
#print axioms leaf00146_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
