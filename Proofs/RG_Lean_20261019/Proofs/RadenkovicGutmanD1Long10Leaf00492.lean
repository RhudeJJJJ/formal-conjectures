/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00492 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 30137061914471356374083174400000000000 30169973529026086679171921838115651584 3693377821500874828068266442752000000000000))
theorem leaf00492_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 30137061914471356374083174400000000000 30169973529026086679171921838115651584 3693377821500874828068266442752000000000000 raw00492=true := by decide +kernel
#print axioms leaf00492_raw
theorem leaf00492_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00492=true := by decide +kernel
#print axioms leaf00492_rectangular
def affine00492 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00492 (IntegerComputedClassCell.leftNumerator ![(3/128),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(3/128),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(3/128),0,0] ![(1/256),1,1]))
theorem leaf00492_transform : affine00492=(NestedInteger.clearedAll 3 raw00492 (IntegerComputedClassCell.leftNumerator ![(3/128),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(3/128),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(3/128),0,0] ![(1/256),1,1])) := by decide +kernel
#print axioms leaf00492_transform
theorem leaf00492_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00492=true := by decide +kernel
#print axioms leaf00492_sign
theorem leaf00492_log : RationalLog.accepts (4299622555/4294967296) (72699/134217728) 0 8=true := by decide +kernel
#print axioms leaf00492_log
def leaf00492 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (8168667/1000000000000) (4299622555/4294967296) (72699/134217728) 0 8 ![52,0,4] ![(3/128),0,0] ![(1/256),1,1] affine00492
theorem leaf00492_checked : FastNestedCellData.accepts 1 0 4 leaf00492=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (8168667/1000000000000) (4299622555/4294967296) (72699/134217728) 0 8 ![52,0,4] ![(3/128),0,0] ![(1/256),1,1] 30137061914471356374083174400000000000 30169973529026086679171921838115651584 3693377821500874828068266442752000000000000 raw00492 affine00492
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00492_raw leaf00492_rectangular
    leaf00492_transform leaf00492_sign leaf00492_log
#print axioms leaf00492_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
