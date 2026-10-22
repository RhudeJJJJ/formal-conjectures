/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00128 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 21264752026964089685332197376000000000000 18689864827912066316239455477709035012096 337772526902293248844058591232000000000000))
theorem leaf00128_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 21264752026964089685332197376000000000000 18689864827912066316239455477709035012096 337772526902293248844058591232000000000000 raw00128=true := by decide +kernel
#print axioms leaf00128_raw
theorem leaf00128_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00128=true := by decide +kernel
#print axioms leaf00128_rectangular
def affine00128 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00128 (IntegerComputedClassCell.leftNumerator ![(3/200),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/200),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/200),0,(1/2)] ![(1/1600),1,(1/2)]))
theorem leaf00128_transform : affine00128=(NestedInteger.clearedAll 3 raw00128 (IntegerComputedClassCell.leftNumerator ![(3/200),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/200),0,(1/2)] ![(1/1600),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/200),0,(1/2)] ![(1/1600),1,(1/2)])) := by decide +kernel
#print axioms leaf00128_transform
theorem leaf00128_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00128=true := by decide +kernel
#print axioms leaf00128_sign
theorem leaf00128_log : RationalLog.accepts (3576978297/4294967296) (-392829659/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00128_log
def leaf00128 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (13833174207/250000000000) (3576978297/4294967296) (-392829659/4294967296) 1 8 ![52,0,4] ![(3/200),0,(1/2)] ![(1/1600),1,(1/2)] affine00128
theorem leaf00128_checked : FastNestedCellData.accepts 1 0 4 leaf00128=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (13833174207/250000000000) (3576978297/4294967296) (-392829659/4294967296) 1 8 ![52,0,4] ![(3/200),0,(1/2)] ![(1/1600),1,(1/2)] 21264752026964089685332197376000000000000 18689864827912066316239455477709035012096 337772526902293248844058591232000000000000 raw00128 affine00128
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00128_raw leaf00128_rectangular
    leaf00128_transform leaf00128_sign leaf00128_log
#print axioms leaf00128_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
