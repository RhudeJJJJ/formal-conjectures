/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00275 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 235145130653350135912231600128000000000000 161394794024614477701857792614126955003904 791322058192573688758579232768000000000000))
theorem leaf00275_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 235145130653350135912231600128000000000000 161394794024614477701857792614126955003904 791322058192573688758579232768000000000000 raw00275=true := by decide +kernel
#print axioms leaf00275_raw
theorem leaf00275_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00275=true := by decide +kernel
#print axioms leaf00275_rectangular
def affine00275 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00275 (IntegerComputedClassCell.leftNumerator ![(39/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(39/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(39/640),0,(1/2)] ![(1/640),1,(1/2)]))
theorem leaf00275_transform : affine00275=(NestedInteger.clearedAll 3 raw00275 (IntegerComputedClassCell.leftNumerator ![(39/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(39/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(39/640),0,(1/2)] ![(1/640),1,(1/2)])) := by decide +kernel
#print axioms leaf00275_transform
theorem leaf00275_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00275=true := by decide +kernel
#print axioms leaf00275_sign
theorem leaf00275_log : RationalLog.accepts (612128819/1073741824) (-603402239/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00275_log
def leaf00275 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (203955889203/1000000000000) (612128819/1073741824) (-603402239/2147483648) 1 8 ![52,0,4] ![(39/640),0,(1/2)] ![(1/640),1,(1/2)] affine00275
theorem leaf00275_checked : FastNestedCellData.accepts 1 0 4 leaf00275=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (203955889203/1000000000000) (612128819/1073741824) (-603402239/2147483648) 1 8 ![52,0,4] ![(39/640),0,(1/2)] ![(1/640),1,(1/2)] 235145130653350135912231600128000000000000 161394794024614477701857792614126955003904 791322058192573688758579232768000000000000 raw00275 affine00275
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00275_raw leaf00275_rectangular
    leaf00275_transform leaf00275_sign leaf00275_log
#print axioms leaf00275_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
