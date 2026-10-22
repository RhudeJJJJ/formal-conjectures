/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00403 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 40498186751315557005704298496000000000000 55418470116038291143604011860196807671808 394419794283239886395080179712000000000000))
theorem leaf00403_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 40498186751315557005704298496000000000000 55418470116038291143604011860196807671808 394419794283239886395080179712000000000000 raw00403=true := by decide +kernel
#print axioms leaf00403_raw
theorem leaf00403_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00403=true := by decide +kernel
#print axioms leaf00403_rectangular
def affine00403 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00403 (IntegerComputedClassCell.leftNumerator ![(7/8),0,(1/2)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/8),0,(1/2)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/8),0,(1/2)] ![(1/8),1,(1/4)]))
theorem leaf00403_transform : affine00403=(NestedInteger.clearedAll 3 raw00403 (IntegerComputedClassCell.leftNumerator ![(7/8),0,(1/2)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/8),0,(1/2)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/8),0,(1/2)] ![(1/8),1,(1/4)])) := by decide +kernel
#print axioms leaf00403_transform
theorem leaf00403_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00403=true := by decide +kernel
#print axioms leaf00403_sign
theorem leaf00403_log : RationalLog.accepts (5153248937/4294967296) (195617975/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00403_log
def leaf00403 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (17563288823/125000000000) (5153248937/4294967296) (195617975/2147483648) 0 8 ![52,0,4] ![(7/8),0,(1/2)] ![(1/8),1,(1/4)] affine00403
theorem leaf00403_checked : FastNestedCellData.accepts 1 0 4 leaf00403=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (17563288823/125000000000) (5153248937/4294967296) (195617975/2147483648) 0 8 ![52,0,4] ![(7/8),0,(1/2)] ![(1/8),1,(1/4)] 40498186751315557005704298496000000000000 55418470116038291143604011860196807671808 394419794283239886395080179712000000000000 raw00403 affine00403
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00403_raw leaf00403_rectangular
    leaf00403_transform leaf00403_sign leaf00403_log
#print axioms leaf00403_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
