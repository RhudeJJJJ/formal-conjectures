/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00225 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 11369338203373508728344287379456000000000000 449313916460792838496390056432300642533376 729011546445951623721685876736000000000000))
theorem leaf00225_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 11369338203373508728344287379456000000000000 449313916460792838496390056432300642533376 729011546445951623721685876736000000000000 raw00225=true := by decide +kernel
#print axioms leaf00225_raw
theorem leaf00225_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00225=true := by decide +kernel
#print axioms leaf00225_rectangular
def affine00225 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00225 (IntegerComputedClassCell.leftNumerator ![(13/320),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/320),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/320),0,0] ![(3/3200),1,(1/4)]))
theorem leaf00225_transform : affine00225=(NestedInteger.clearedAll 3 raw00225 (IntegerComputedClassCell.leftNumerator ![(13/320),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/320),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/320),0,0] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00225_transform
theorem leaf00225_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00225=true := by decide +kernel
#print axioms leaf00225_sign
theorem leaf00225_log : RationalLog.accepts (105013151/4294967296) (-498097253/268435456) 6 8=true := by decide +kernel
#print axioms leaf00225_log
def leaf00225 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (616333058991/1000000000000) (105013151/4294967296) (-498097253/268435456) 6 8 ![52,0,4] ![(13/320),0,0] ![(3/3200),1,(1/4)] affine00225
theorem leaf00225_checked : FastNestedCellData.accepts 1 0 4 leaf00225=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (616333058991/1000000000000) (105013151/4294967296) (-498097253/268435456) 6 8 ![52,0,4] ![(13/320),0,0] ![(3/3200),1,(1/4)] 11369338203373508728344287379456000000000000 449313916460792838496390056432300642533376 729011546445951623721685876736000000000000 raw00225 affine00225
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00225_raw leaf00225_rectangular
    leaf00225_transform leaf00225_sign leaf00225_log
#print axioms leaf00225_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
