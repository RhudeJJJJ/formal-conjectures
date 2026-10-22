/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00276 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 12763377927510113329012023492608000000000000 1244049345568449176963187519056528743071744 1798008334713933592767064178688000000000000))
theorem leaf00276_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 12763377927510113329012023492608000000000000 1244049345568449176963187519056528743071744 1798008334713933592767064178688000000000000 raw00276=true := by decide +kernel
#print axioms leaf00276_raw
theorem leaf00276_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00276=true := by decide +kernel
#print axioms leaf00276_rectangular
def affine00276 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00276 (IntegerComputedClassCell.leftNumerator ![(1/16),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/16),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/16),0,0] ![(1/640),1,(1/4)]))
theorem leaf00276_transform : affine00276=(NestedInteger.clearedAll 3 raw00276 (IntegerComputedClassCell.leftNumerator ![(1/16),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/16),0,0] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/16),0,0] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00276_transform
theorem leaf00276_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00276=true := by decide +kernel
#print axioms leaf00276_sign
theorem leaf00276_log : RationalLog.accepts (247432131/4294967296) (-1532263393/1073741824) 5 8=true := by decide +kernel
#print axioms leaf00276_log
def leaf00276 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (691904103863/1000000000000) (247432131/4294967296) (-1532263393/1073741824) 5 8 ![52,0,4] ![(1/16),0,0] ![(1/640),1,(1/4)] affine00276
theorem leaf00276_checked : FastNestedCellData.accepts 1 0 4 leaf00276=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (691904103863/1000000000000) (247432131/4294967296) (-1532263393/1073741824) 5 8 ![52,0,4] ![(1/16),0,0] ![(1/640),1,(1/4)] 12763377927510113329012023492608000000000000 1244049345568449176963187519056528743071744 1798008334713933592767064178688000000000000 raw00276 affine00276
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00276_raw leaf00276_rectangular
    leaf00276_transform leaf00276_sign leaf00276_log
#print axioms leaf00276_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
