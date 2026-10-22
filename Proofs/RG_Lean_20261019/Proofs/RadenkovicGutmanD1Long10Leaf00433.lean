/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00433 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 6194279277825178480767139840000000000 7095720635912530491607425428611923968 528281567226876666033817518080000000000))
theorem leaf00433_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 6194279277825178480767139840000000000 7095720635912530491607425428611923968 528281567226876666033817518080000000000 raw00433=true := by decide +kernel
#print axioms leaf00433_raw
theorem leaf00433_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00433=true := by decide +kernel
#print axioms leaf00433_rectangular
def affine00433 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00433 (IntegerComputedClassCell.leftNumerator ![(5/16),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/16),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/16),0,(1/2)] ![(1/32),1,(1/4)]))
theorem leaf00433_transform : affine00433=(NestedInteger.clearedAll 3 raw00433 (IntegerComputedClassCell.leftNumerator ![(5/16),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/16),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/16),0,(1/2)] ![(1/32),1,(1/4)])) := by decide +kernel
#print axioms leaf00433_transform
theorem leaf00433_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00433=true := by decide +kernel
#print axioms leaf00433_sign
theorem leaf00433_log : RationalLog.accepts (2427398651/2147483648) (131558509/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00433_log
def leaf00433 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (134317021/10000000000) (2427398651/2147483648) (131558509/2147483648) 0 8 ![52,0,4] ![(5/16),0,(1/2)] ![(1/32),1,(1/4)] affine00433
theorem leaf00433_checked : FastNestedCellData.accepts 1 0 4 leaf00433=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (134317021/10000000000) (2427398651/2147483648) (131558509/2147483648) 0 8 ![52,0,4] ![(5/16),0,(1/2)] ![(1/32),1,(1/4)] 6194279277825178480767139840000000000 7095720635912530491607425428611923968 528281567226876666033817518080000000000 raw00433 affine00433
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00433_raw leaf00433_rectangular
    leaf00433_transform leaf00433_sign leaf00433_log
#print axioms leaf00433_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
