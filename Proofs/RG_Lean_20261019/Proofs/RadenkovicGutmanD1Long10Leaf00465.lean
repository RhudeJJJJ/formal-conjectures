/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00465 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 320739066315281059171794944000000000000 330128425744137252692931352386921824256 296668071724918271966976147456000000000000))
theorem leaf00465_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 320739066315281059171794944000000000000 330128425744137252692931352386921824256 296668071724918271966976147456000000000000 raw00465=true := by decide +kernel
#print axioms leaf00465_raw
theorem leaf00465_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00465=true := by decide +kernel
#print axioms leaf00465_rectangular
def affine00465 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00465 (IntegerComputedClassCell.leftNumerator ![(1/8),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/8),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/8),0,0] ![(1/64),1,(1/2)]))
theorem leaf00465_transform : affine00465=(NestedInteger.clearedAll 3 raw00465 (IntegerComputedClassCell.leftNumerator ![(1/8),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/8),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/8),0,0] ![(1/64),1,(1/2)])) := by decide +kernel
#print axioms leaf00465_transform
theorem leaf00465_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00465=true := by decide +kernel
#print axioms leaf00465_sign
theorem leaf00465_log : RationalLog.accepts (4415784929/4294967296) (29787385/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00465_log
def leaf00465 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (139098397/125000000000) (4415784929/4294967296) (29787385/2147483648) 0 8 ![52,0,4] ![(1/8),0,0] ![(1/64),1,(1/2)] affine00465
theorem leaf00465_checked : FastNestedCellData.accepts 1 0 4 leaf00465=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (139098397/125000000000) (4415784929/4294967296) (29787385/2147483648) 0 8 ![52,0,4] ![(1/8),0,0] ![(1/64),1,(1/2)] 320739066315281059171794944000000000000 330128425744137252692931352386921824256 296668071724918271966976147456000000000000 raw00465 affine00465
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00465_raw leaf00465_rectangular
    leaf00465_transform leaf00465_sign leaf00465_log
#print axioms leaf00465_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
