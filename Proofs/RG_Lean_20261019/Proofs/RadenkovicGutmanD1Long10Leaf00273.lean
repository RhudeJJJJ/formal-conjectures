/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00273 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 794523629378972739240015691776000000000000 73622878822233772825605551576968253669376 106833072153642027665720344576000000000000))
theorem leaf00273_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 794523629378972739240015691776000000000000 73622878822233772825605551576968253669376 106833072153642027665720344576000000000000 raw00273=true := by decide +kernel
#print axioms leaf00273_raw
theorem leaf00273_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00273=true := by decide +kernel
#print axioms leaf00273_rectangular
def affine00273 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00273 (IntegerComputedClassCell.leftNumerator ![(39/640),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(39/640),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(39/640),0,0] ![(1/640),1,(1/4)]))
theorem leaf00273_transform : affine00273=(NestedInteger.clearedAll 3 raw00273 (IntegerComputedClassCell.leftNumerator ![(39/640),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(39/640),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(39/640),0,0] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00273_transform
theorem leaf00273_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00273=true := by decide +kernel
#print axioms leaf00273_sign
theorem leaf00273_log : RationalLog.accepts (58903399/1073741824) (-6234158225/4294967296) 5 8=true := by decide +kernel
#print axioms leaf00273_log
def leaf00273 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (689139396051/1000000000000) (58903399/1073741824) (-6234158225/4294967296) 5 8 ![52,0,4] ![(39/640),0,0] ![(1/640),1,(1/4)] affine00273
theorem leaf00273_checked : FastNestedCellData.accepts 1 0 4 leaf00273=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (689139396051/1000000000000) (58903399/1073741824) (-6234158225/4294967296) 5 8 ![52,0,4] ![(39/640),0,0] ![(1/640),1,(1/4)] 794523629378972739240015691776000000000000 73622878822233772825605551576968253669376 106833072153642027665720344576000000000000 raw00273 affine00273
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00273_raw leaf00273_rectangular
    leaf00273_transform leaf00273_sign leaf00273_log
#print axioms leaf00273_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
