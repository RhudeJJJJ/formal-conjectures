/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00317 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 20661752886979553439785156608000000000000 13463642730370327631800674633028544233472 46954278634708209760861159424000000000000))
theorem leaf00317_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 20661752886979553439785156608000000000000 13463642730370327631800674633028544233472 46954278634708209760861159424000000000000 raw00317=true := by decide +kernel
#print axioms leaf00317_raw
theorem leaf00317_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00317=true := by decide +kernel
#print axioms leaf00317_rectangular
def affine00317 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00317 (IntegerComputedClassCell.leftNumerator ![(31/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(31/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(31/320),0,(1/2)] ![(1/320),1,(1/2)]))
theorem leaf00317_transform : affine00317=(NestedInteger.clearedAll 3 raw00317 (IntegerComputedClassCell.leftNumerator ![(31/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(31/320),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(31/320),0,(1/2)] ![(1/320),1,(1/2)])) := by decide +kernel
#print axioms leaf00317_transform
theorem leaf00317_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00317=true := by decide +kernel
#print axioms leaf00317_sign
theorem leaf00317_log : RationalLog.accepts (135939193/268435456) (-1461153971/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00317_log
def leaf00317 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (286739422303/1000000000000) (135939193/268435456) (-1461153971/4294967296) 1 8 ![52,0,4] ![(31/320),0,(1/2)] ![(1/320),1,(1/2)] affine00317
theorem leaf00317_checked : FastNestedCellData.accepts 1 0 4 leaf00317=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (286739422303/1000000000000) (135939193/268435456) (-1461153971/4294967296) 1 8 ![52,0,4] ![(31/320),0,(1/2)] ![(1/320),1,(1/2)] 20661752886979553439785156608000000000000 13463642730370327631800674633028544233472 46954278634708209760861159424000000000000 raw00317 affine00317
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00317_raw leaf00317_rectangular
    leaf00317_transform leaf00317_sign leaf00317_log
#print axioms leaf00317_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
