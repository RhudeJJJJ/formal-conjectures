/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00431 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 77732209018541486427038810112000000000000 90751075697864607194270670850285425917952 5384067585847960366311941341184000000000000))
theorem leaf00431_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 77732209018541486427038810112000000000000 90751075697864607194270670850285425917952 5384067585847960366311941341184000000000000 raw00431=true := by decide +kernel
#print axioms leaf00431_raw
theorem leaf00431_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00431=true := by decide +kernel
#print axioms leaf00431_rectangular
def affine00431 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00431 (IntegerComputedClassCell.leftNumerator ![(11/32),0,(3/4)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/32),0,(3/4)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/32),0,(3/4)] ![(1/32),1,(1/4)]))
theorem leaf00431_transform : affine00431=(NestedInteger.clearedAll 3 raw00431 (IntegerComputedClassCell.leftNumerator ![(11/32),0,(3/4)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/32),0,(3/4)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/32),0,(3/4)] ![(1/32),1,(1/4)])) := by decide +kernel
#print axioms leaf00431_transform
theorem leaf00431_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00431=true := by decide +kernel
#print axioms leaf00431_sign
theorem leaf00431_log : RationalLog.accepts (4931186147/4294967296) (37080497/536870912) 0 8=true := by decide +kernel
#print axioms leaf00431_log
def leaf00431 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (8427742989/500000000000) (4931186147/4294967296) (37080497/536870912) 0 8 ![52,0,4] ![(11/32),0,(3/4)] ![(1/32),1,(1/4)] affine00431
theorem leaf00431_checked : FastNestedCellData.accepts 1 0 4 leaf00431=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (8427742989/500000000000) (4931186147/4294967296) (37080497/536870912) 0 8 ![52,0,4] ![(11/32),0,(3/4)] ![(1/32),1,(1/4)] 77732209018541486427038810112000000000000 90751075697864607194270670850285425917952 5384067585847960366311941341184000000000000 raw00431 affine00431
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00431_raw leaf00431_rectangular
    leaf00431_transform leaf00431_sign leaf00431_log
#print axioms leaf00431_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
