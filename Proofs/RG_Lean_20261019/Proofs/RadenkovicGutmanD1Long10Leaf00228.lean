/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00228 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2866760442902133471960841060352000000000000 119093722342179107194344549179649819672576 191583100557890036978524618752000000000000))
theorem leaf00228_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2866760442902133471960841060352000000000000 119093722342179107194344549179649819672576 191583100557890036978524618752000000000000 raw00228=true := by decide +kernel
#print axioms leaf00228_raw
theorem leaf00228_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00228=true := by decide +kernel
#print axioms leaf00228_rectangular
def affine00228 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00228 (IntegerComputedClassCell.leftNumerator ![(133/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(133/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(133/3200),0,0] ![(3/3200),1,(1/4)]))
theorem leaf00228_transform : affine00228=(NestedInteger.clearedAll 3 raw00228 (IntegerComputedClassCell.leftNumerator ![(133/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(133/3200),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(133/3200),0,0] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00228_transform
theorem leaf00228_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00228=true := by decide +kernel
#print axioms leaf00228_sign
theorem leaf00228_log : RationalLog.accepts (110028621/4294967296) (-7869365343/4294967296) 6 8=true := by decide +kernel
#print axioms leaf00228_log
def leaf00228 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (310814790019/500000000000) (110028621/4294967296) (-7869365343/4294967296) 6 8 ![52,0,4] ![(133/3200),0,0] ![(3/3200),1,(1/4)] affine00228
theorem leaf00228_checked : FastNestedCellData.accepts 1 0 4 leaf00228=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (310814790019/500000000000) (110028621/4294967296) (-7869365343/4294967296) 6 8 ![52,0,4] ![(133/3200),0,0] ![(3/3200),1,(1/4)] 2866760442902133471960841060352000000000000 119093722342179107194344549179649819672576 191583100557890036978524618752000000000000 raw00228 affine00228
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00228_raw leaf00228_rectangular
    leaf00228_transform leaf00228_sign leaf00228_log
#print axioms leaf00228_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
