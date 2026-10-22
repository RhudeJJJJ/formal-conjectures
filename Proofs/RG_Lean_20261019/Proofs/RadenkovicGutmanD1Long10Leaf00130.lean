/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00130 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2187705937816419599356507717632000000000000 1675873814159712654807724446822586883506176 14130973827539097578775655743488000000000000))
theorem leaf00130_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2187705937816419599356507717632000000000000 1675873814159712654807724446822586883506176 14130973827539097578775655743488000000000000 raw00130=true := by decide +kernel
#print axioms leaf00130_raw
theorem leaf00130_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00130=true := by decide +kernel
#print axioms leaf00130_rectangular
def affine00130 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00130 (IntegerComputedClassCell.leftNumerator ![(1/64),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/64),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/64),0,(1/4)] ![(1/1600),1,(1/4)]))
theorem leaf00130_transform : affine00130=(NestedInteger.clearedAll 3 raw00130 (IntegerComputedClassCell.leftNumerator ![(1/64),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/64),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/64),0,(1/4)] ![(1/1600),1,(1/4)])) := by decide +kernel
#print axioms leaf00130_transform
theorem leaf00130_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00130=true := by decide +kernel
#print axioms leaf00130_sign
theorem leaf00130_log : RationalLog.accepts (2941298189/4294967296) (-406511045/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00130_log
def leaf00130 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (118595776527/1000000000000) (2941298189/4294967296) (-406511045/2147483648) 1 8 ![52,0,4] ![(1/64),0,(1/4)] ![(1/1600),1,(1/4)] affine00130
theorem leaf00130_checked : FastNestedCellData.accepts 1 0 4 leaf00130=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (118595776527/1000000000000) (2941298189/4294967296) (-406511045/2147483648) 1 8 ![52,0,4] ![(1/64),0,(1/4)] ![(1/1600),1,(1/4)] 2187705937816419599356507717632000000000000 1675873814159712654807724446822586883506176 14130973827539097578775655743488000000000000 raw00130 affine00130
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00130_raw leaf00130_rectangular
    leaf00130_transform leaf00130_sign leaf00130_log
#print axioms leaf00130_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
