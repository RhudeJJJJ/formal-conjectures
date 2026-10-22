/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00302 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 24560432943359571968147849216000000000000 16123395957379915966619831670093920600064 63072347467108797122810478592000000000000))
theorem leaf00302_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 24560432943359571968147849216000000000000 16123395957379915966619831670093920600064 63072347467108797122810478592000000000000 raw00302=true := by decide +kernel
#print axioms leaf00302_raw
theorem leaf00302_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00302=true := by decide +kernel
#print axioms leaf00302_rectangular
def affine00302 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00302 (IntegerComputedClassCell.leftNumerator ![(13/160),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/160),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/160),0,(1/2)] ![(1/320),1,(1/2)]))
theorem leaf00302_transform : affine00302=(NestedInteger.clearedAll 3 raw00302 (IntegerComputedClassCell.leftNumerator ![(13/160),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/160),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/160),0,(1/2)] ![(1/320),1,(1/2)])) := by decide +kernel
#print axioms leaf00302_transform
theorem leaf00302_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00302=true := by decide +kernel
#print axioms leaf00302_sign
theorem leaf00302_log : RationalLog.accepts (561380763/1073741824) (-696327455/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00302_log
def leaf00302 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (127816678821/500000000000) (561380763/1073741824) (-696327455/2147483648) 1 8 ![52,0,4] ![(13/160),0,(1/2)] ![(1/320),1,(1/2)] affine00302
theorem leaf00302_checked : FastNestedCellData.accepts 1 0 4 leaf00302=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (127816678821/500000000000) (561380763/1073741824) (-696327455/2147483648) 1 8 ![52,0,4] ![(13/160),0,(1/2)] ![(1/320),1,(1/2)] 24560432943359571968147849216000000000000 16123395957379915966619831670093920600064 63072347467108797122810478592000000000000 raw00302 affine00302
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00302_raw leaf00302_rectangular
    leaf00302_transform leaf00302_sign leaf00302_log
#print axioms leaf00302_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
