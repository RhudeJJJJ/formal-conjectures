/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00321 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 3236802802234672047407887286272000000000000 800231871284852616984635006816476224028672 1140143023157448512842397384704000000000000))
theorem leaf00321_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 3236802802234672047407887286272000000000000 800231871284852616984635006816476224028672 1140143023157448512842397384704000000000000 raw00321=true := by decide +kernel
#print axioms leaf00321_raw
theorem leaf00321_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00321=true := by decide +kernel
#print axioms leaf00321_rectangular
def affine00321 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00321 (IntegerComputedClassCell.leftNumerator ![(33/320),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(33/320),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(33/320),0,0] ![(1/320),1,(1/4)]))
theorem leaf00321_transform : affine00321=(NestedInteger.clearedAll 3 raw00321 (IntegerComputedClassCell.leftNumerator ![(33/320),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(33/320),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(33/320),0,0] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00321_transform
theorem leaf00321_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00321=true := by decide +kernel
#print axioms leaf00321_sign
theorem leaf00321_log : RationalLog.accepts (623926097/4294967296) (-2071427661/2147483648) 3 8=true := by decide +kernel
#print axioms leaf00321_log
def leaf00321 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (350934863009/500000000000) (623926097/4294967296) (-2071427661/2147483648) 3 8 ![52,0,4] ![(33/320),0,0] ![(1/320),1,(1/4)] affine00321
theorem leaf00321_checked : FastNestedCellData.accepts 1 0 4 leaf00321=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (350934863009/500000000000) (623926097/4294967296) (-2071427661/2147483648) 3 8 ![52,0,4] ![(33/320),0,0] ![(1/320),1,(1/4)] 3236802802234672047407887286272000000000000 800231871284852616984635006816476224028672 1140143023157448512842397384704000000000000 raw00321 affine00321
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00321_raw leaf00321_rectangular
    leaf00321_transform leaf00321_sign leaf00321_log
#print axioms leaf00321_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
