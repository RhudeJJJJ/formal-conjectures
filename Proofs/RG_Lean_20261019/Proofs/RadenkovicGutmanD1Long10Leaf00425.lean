/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00425 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 114176590304383525204162248704000000000000 138180126620027706125927779257718551871488 5581208514453619286363904933888000000000000))
theorem leaf00425_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 114176590304383525204162248704000000000000 138180126620027706125927779257718551871488 5581208514453619286363904933888000000000000 raw00425=true := by decide +kernel
#print axioms leaf00425_raw
theorem leaf00425_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00425=true := by decide +kernel
#print axioms leaf00425_rectangular
def affine00425 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00425 (IntegerComputedClassCell.leftNumerator ![(13/32),0,(3/4)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/32),0,(3/4)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/32),0,(3/4)] ![(1/32),1,(1/4)]))
theorem leaf00425_transform : affine00425=(NestedInteger.clearedAll 3 raw00425 (IntegerComputedClassCell.leftNumerator ![(13/32),0,(3/4)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/32),0,(3/4)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/32),0,(3/4)] ![(1/32),1,(1/4)])) := by decide +kernel
#print axioms leaf00425_transform
theorem leaf00425_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00425=true := by decide +kernel
#print axioms leaf00425_sign
theorem leaf00425_log : RationalLog.accepts (2536162181/2147483648) (178622563/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00425_log
def leaf00425 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (24758101451/1000000000000) (2536162181/2147483648) (178622563/2147483648) 0 8 ![52,0,4] ![(13/32),0,(3/4)] ![(1/32),1,(1/4)] affine00425
theorem leaf00425_checked : FastNestedCellData.accepts 1 0 4 leaf00425=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (24758101451/1000000000000) (2536162181/2147483648) (178622563/2147483648) 0 8 ![52,0,4] ![(13/32),0,(3/4)] ![(1/32),1,(1/4)] 114176590304383525204162248704000000000000 138180126620027706125927779257718551871488 5581208514453619286363904933888000000000000 raw00425 affine00425
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00425_raw leaf00425_rectangular
    leaf00425_transform leaf00425_sign leaf00425_log
#print axioms leaf00425_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
