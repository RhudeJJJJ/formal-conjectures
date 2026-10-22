/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00409 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 1778961223466638137374644633600000000000 2435535703333939504516051554501365071872 26307313977869104876137480192000000000000))
theorem leaf00409_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 1778961223466638137374644633600000000000 2435535703333939504516051554501365071872 26307313977869104876137480192000000000000 raw00409=true := by decide +kernel
#print axioms leaf00409_raw
theorem leaf00409_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00409=true := by decide +kernel
#print axioms leaf00409_rectangular
def affine00409 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00409 (IntegerComputedClassCell.leftNumerator ![(3/4),0,(1/2)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,(1/2)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/4),0,(1/2)] ![(1/8),1,(1/4)]))
theorem leaf00409_transform : affine00409=(NestedInteger.clearedAll 3 raw00409 (IntegerComputedClassCell.leftNumerator ![(3/4),0,(1/2)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,(1/2)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/4),0,(1/2)] ![(1/8),1,(1/4)])) := by decide +kernel
#print axioms leaf00409_transform
theorem leaf00409_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00409=true := by decide +kernel
#print axioms leaf00409_sign
theorem leaf00409_log : RationalLog.accepts (2690943435/2147483648) (484461769/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00409_log
def leaf00409 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (23145043479/250000000000) (2690943435/2147483648) (484461769/4294967296) 0 8 ![52,0,4] ![(3/4),0,(1/2)] ![(1/8),1,(1/4)] affine00409
theorem leaf00409_checked : FastNestedCellData.accepts 1 0 4 leaf00409=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (23145043479/250000000000) (2690943435/2147483648) (484461769/4294967296) 0 8 ![52,0,4] ![(3/4),0,(1/2)] ![(1/8),1,(1/4)] 1778961223466638137374644633600000000000 2435535703333939504516051554501365071872 26307313977869104876137480192000000000000 raw00409 affine00409
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00409_raw leaf00409_rectangular
    leaf00409_transform leaf00409_sign leaf00409_log
#print axioms leaf00409_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
