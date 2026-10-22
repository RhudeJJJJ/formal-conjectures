/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00452 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 1195075278400000893342711808000000000000 1280241505884911529915447259383398924288 308770918013026867709827088384000000000000))
theorem leaf00452_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 1195075278400000893342711808000000000000 1280241505884911529915447259383398924288 308770918013026867709827088384000000000000 raw00452=true := by decide +kernel
#print axioms leaf00452_raw
theorem leaf00452_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00452=true := by decide +kernel
#print axioms leaf00452_rectangular
def affine00452 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00452 (IntegerComputedClassCell.leftNumerator ![(13/64),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/64),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/64),0,(3/4)] ![(1/64),1,(1/4)]))
theorem leaf00452_transform : affine00452=(NestedInteger.clearedAll 3 raw00452 (IntegerComputedClassCell.leftNumerator ![(13/64),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/64),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/64),0,(3/4)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf00452_transform
theorem leaf00452_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00452=true := by decide +kernel
#print axioms leaf00452_sign
theorem leaf00452_log : RationalLog.accepts (1145511727/1073741824) (69473115/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00452_log
def leaf00452 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (2073125141/500000000000) (1145511727/1073741824) (69473115/2147483648) 0 8 ![52,0,4] ![(13/64),0,(3/4)] ![(1/64),1,(1/4)] affine00452
theorem leaf00452_checked : FastNestedCellData.accepts 1 0 4 leaf00452=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (2073125141/500000000000) (1145511727/1073741824) (69473115/2147483648) 0 8 ![52,0,4] ![(13/64),0,(3/4)] ![(1/64),1,(1/4)] 1195075278400000893342711808000000000000 1280241505884911529915447259383398924288 308770918013026867709827088384000000000000 raw00452 affine00452
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00452_raw leaf00452_rectangular
    leaf00452_transform leaf00452_sign leaf00452_log
#print axioms leaf00452_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
