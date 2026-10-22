/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00335 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 380865826655148918477735067648000000000000 253754842230459677955522373160090023755776 768142989028284718499823091712000000000000))
theorem leaf00335_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 380865826655148918477735067648000000000000 253754842230459677955522373160090023755776 768142989028284718499823091712000000000000 raw00335=true := by decide +kernel
#print axioms leaf00335_raw
theorem leaf00335_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00335=true := by decide +kernel
#print axioms leaf00335_rectangular
def affine00335 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00335 (IntegerComputedClassCell.leftNumerator ![(1/8),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/8),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/8),0,(1/2)] ![(1/160),1,(1/2)]))
theorem leaf00335_transform : affine00335=(NestedInteger.clearedAll 3 raw00335 (IntegerComputedClassCell.leftNumerator ![(1/8),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/8),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/8),0,(1/2)] ![(1/160),1,(1/2)])) := by decide +kernel
#print axioms leaf00335_transform
theorem leaf00335_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00335=true := by decide +kernel
#print axioms leaf00335_sign
theorem leaf00335_log : RationalLog.accepts (2150982049/4294967296) (-1485026717/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00335_log
def leaf00335 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (82587111337/250000000000) (2150982049/4294967296) (-1485026717/4294967296) 1 8 ![52,0,4] ![(1/8),0,(1/2)] ![(1/160),1,(1/2)] affine00335
theorem leaf00335_checked : FastNestedCellData.accepts 1 0 4 leaf00335=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (82587111337/250000000000) (2150982049/4294967296) (-1485026717/4294967296) 1 8 ![52,0,4] ![(1/8),0,(1/2)] ![(1/160),1,(1/2)] 380865826655148918477735067648000000000000 253754842230459677955522373160090023755776 768142989028284718499823091712000000000000 raw00335 affine00335
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00335_raw leaf00335_rectangular
    leaf00335_transform leaf00335_sign leaf00335_log
#print axioms leaf00335_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
