/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00450 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 597537682146326493276405760000000000 640120800815714057873747800926191616 154385459456653017308410675200000000000))
theorem leaf00450_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 597537682146326493276405760000000000 640120800815714057873747800926191616 154385459456653017308410675200000000000 raw00450=true := by decide +kernel
#print axioms leaf00450_raw
theorem leaf00450_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00450=true := by decide +kernel
#print axioms leaf00450_rectangular
def affine00450 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00450 (IntegerComputedClassCell.leftNumerator ![(13/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/64),0,0] ![(1/64),1,(1/2)]))
theorem leaf00450_transform : affine00450=(NestedInteger.clearedAll 3 raw00450 (IntegerComputedClassCell.leftNumerator ![(13/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/64),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/64),0,0] ![(1/64),1,(1/2)])) := by decide +kernel
#print axioms leaf00450_transform
theorem leaf00450_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00450=true := by decide +kernel
#print axioms leaf00450_sign
theorem leaf00450_log : RationalLog.accepts (572755865/536870912) (138946235/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00450_log
def leaf00450 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (207312529/50000000000) (572755865/536870912) (138946235/4294967296) 0 8 ![52,0,4] ![(13/64),0,0] ![(1/64),1,(1/2)] affine00450
theorem leaf00450_checked : FastNestedCellData.accepts 1 0 4 leaf00450=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (207312529/50000000000) (572755865/536870912) (138946235/4294967296) 0 8 ![52,0,4] ![(13/64),0,0] ![(1/64),1,(1/2)] 597537682146326493276405760000000000 640120800815714057873747800926191616 154385459456653017308410675200000000000 raw00450 affine00450
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00450_raw leaf00450_rectangular
    leaf00450_transform leaf00450_sign leaf00450_log
#print axioms leaf00450_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
