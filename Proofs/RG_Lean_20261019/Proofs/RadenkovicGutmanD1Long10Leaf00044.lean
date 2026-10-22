/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00044 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 5040885761966198690884354048000000000000 4823933978092073282142685324931357474816 275825394720743274982720667648000000000000))
theorem leaf00044_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 5040885761966198690884354048000000000000 4823933978092073282142685324931357474816 275825394720743274982720667648000000000000 raw00044=true := by decide +kernel
#print axioms leaf00044_raw
theorem leaf00044_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00044=true := by decide +kernel
#print axioms leaf00044_rectangular
def affine00044 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00044 (IntegerComputedClassCell.leftNumerator ![(37/8000),0,(1/2)] ![(3/8000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(37/8000),0,(1/2)] ![(3/8000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(37/8000),0,(1/2)] ![(3/8000),1,(1/2)]))
theorem leaf00044_transform : affine00044=(NestedInteger.clearedAll 3 raw00044 (IntegerComputedClassCell.leftNumerator ![(37/8000),0,(1/2)] ![(3/8000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(37/8000),0,(1/2)] ![(3/8000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(37/8000),0,(1/2)] ![(3/8000),1,(1/2)])) := by decide +kernel
#print axioms leaf00044_transform
theorem leaf00044_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00044=true := by decide +kernel
#print axioms leaf00044_sign
theorem leaf00044_log : RationalLog.accepts (1009867999/1073741824) (-8231569/268435456) 1 8=true := by decide +kernel
#print axioms leaf00044_log
def leaf00044 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (8744542871/500000000000) (1009867999/1073741824) (-8231569/268435456) 1 8 ![52,0,4] ![(37/8000),0,(1/2)] ![(3/8000),1,(1/2)] affine00044
theorem leaf00044_checked : FastNestedCellData.accepts 1 0 4 leaf00044=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (8744542871/500000000000) (1009867999/1073741824) (-8231569/268435456) 1 8 ![52,0,4] ![(37/8000),0,(1/2)] ![(3/8000),1,(1/2)] 5040885761966198690884354048000000000000 4823933978092073282142685324931357474816 275825394720743274982720667648000000000000 raw00044 affine00044
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00044_raw leaf00044_rectangular
    leaf00044_transform leaf00044_sign leaf00044_log
#print axioms leaf00044_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
