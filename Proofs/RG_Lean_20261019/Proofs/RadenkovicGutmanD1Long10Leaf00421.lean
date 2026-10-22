/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00421 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 907742672424093711924723712000000000 1118992643161900249734631809471217664 35530737977565192364281036800000000000))
theorem leaf00421_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 907742672424093711924723712000000000 1118992643161900249734631809471217664 35530737977565192364281036800000000000 raw00421=true := by decide +kernel
#print axioms leaf00421_raw
theorem leaf00421_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00421=true := by decide +kernel
#print axioms leaf00421_rectangular
def affine00421 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00421 (IntegerComputedClassCell.leftNumerator ![(7/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/16),0,(1/2)] ![(1/16),1,(1/4)]))
theorem leaf00421_transform : affine00421=(NestedInteger.clearedAll 3 raw00421 (IntegerComputedClassCell.leftNumerator ![(7/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/16),0,(1/2)] ![(1/16),1,(1/4)])) := by decide +kernel
#print axioms leaf00421_transform
theorem leaf00421_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00421=true := by decide +kernel
#print axioms leaf00421_sign
theorem leaf00421_log : RationalLog.accepts (2566420325/2147483648) (191357219/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00421_log
def leaf00421 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (393670631/12500000000) (2566420325/2147483648) (191357219/2147483648) 0 8 ![52,0,4] ![(7/16),0,(1/2)] ![(1/16),1,(1/4)] affine00421
theorem leaf00421_checked : FastNestedCellData.accepts 1 0 4 leaf00421=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (393670631/12500000000) (2566420325/2147483648) (191357219/2147483648) 0 8 ![52,0,4] ![(7/16),0,(1/2)] ![(1/16),1,(1/4)] 907742672424093711924723712000000000 1118992643161900249734631809471217664 35530737977565192364281036800000000000 raw00421 affine00421
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00421_raw leaf00421_rectangular
    leaf00421_transform leaf00421_sign leaf00421_log
#print axioms leaf00421_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
