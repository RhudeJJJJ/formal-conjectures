/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00063 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 186916879911029200569021497344000000000000 78866227874314897764864028929742077952 486454568184541913030852608000000000000))
theorem leaf00063_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 186916879911029200569021497344000000000000 78866227874314897764864028929742077952 486454568184541913030852608000000000000 raw00063=true := by decide +kernel
#print axioms leaf00063_raw
theorem leaf00063_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00063=true := by decide +kernel
#print axioms leaf00063_rectangular
def affine00063 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00063 (IntegerComputedClassCell.leftNumerator ![(11/1600),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/1600),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/1600),0,0] ![(1/3200),1,(1/4)]))
theorem leaf00063_transform : affine00063=(NestedInteger.clearedAll 3 raw00063 (IntegerComputedClassCell.leftNumerator ![(11/1600),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/1600),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/1600),0,0] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00063_transform
theorem leaf00063_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00063=true := by decide +kernel
#print axioms leaf00063_sign
theorem leaf00063_log : RationalLog.accepts (389843/1073741824) (-17010038105/4294967296) 12 8=true := by decide +kernel
#print axioms leaf00063_log
def leaf00063 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (162124549819/1000000000000) (389843/1073741824) (-17010038105/4294967296) 12 8 ![52,0,4] ![(11/1600),0,0] ![(1/3200),1,(1/4)] affine00063
theorem leaf00063_checked : FastNestedCellData.accepts 1 0 4 leaf00063=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (162124549819/1000000000000) (389843/1073741824) (-17010038105/4294967296) 12 8 ![52,0,4] ![(11/1600),0,0] ![(1/3200),1,(1/4)] 186916879911029200569021497344000000000000 78866227874314897764864028929742077952 486454568184541913030852608000000000000 raw00063 affine00063
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00063_raw leaf00063_rectangular
    leaf00063_transform leaf00063_sign leaf00063_log
#print axioms leaf00063_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
