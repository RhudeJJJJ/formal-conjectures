/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00442 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 14683978305912177626231865344000000000000 16175908688978447201696622533328959963136 2257886804915643352273393811456000000000000))
theorem leaf00442_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 14683978305912177626231865344000000000000 16175908688978447201696622533328959963136 2257886804915643352273393811456000000000000 raw00442=true := by decide +kernel
#print axioms leaf00442_raw
theorem leaf00442_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00442=true := by decide +kernel
#print axioms leaf00442_rectangular
def affine00442 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00442 (IntegerComputedClassCell.leftNumerator ![(1/4),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/4),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/4),0,(1/2)] ![(1/64),1,(1/4)]))
theorem leaf00442_transform : affine00442=(NestedInteger.clearedAll 3 raw00442 (IntegerComputedClassCell.leftNumerator ![(1/4),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/4),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/4),0,(1/2)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf00442_transform
theorem leaf00442_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00442=true := by decide +kernel
#print axioms leaf00442_sign
theorem leaf00442_log : RationalLog.accepts (4697692029/4294967296) (192473353/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00442_log
def leaf00442 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (7164180531/1000000000000) (4697692029/4294967296) (192473353/4294967296) 0 8 ![52,0,4] ![(1/4),0,(1/2)] ![(1/64),1,(1/4)] affine00442
theorem leaf00442_checked : FastNestedCellData.accepts 1 0 4 leaf00442=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (7164180531/1000000000000) (4697692029/4294967296) (192473353/4294967296) 0 8 ![52,0,4] ![(1/4),0,(1/2)] ![(1/64),1,(1/4)] 14683978305912177626231865344000000000000 16175908688978447201696622533328959963136 2257886804915643352273393811456000000000000 raw00442 affine00442
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00442_raw leaf00442_rectangular
    leaf00442_transform leaf00442_sign leaf00442_log
#print axioms leaf00442_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
