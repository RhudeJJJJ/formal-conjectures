/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00445 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 27919643497490511655293943808000000000000 30465972691845501494766108490205711302656 5032281315246842653259310563328000000000000))
theorem leaf00445_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 27919643497490511655293943808000000000000 30465972691845501494766108490205711302656 5032281315246842653259310563328000000000000 raw00445=true := by decide +kernel
#print axioms leaf00445_raw
theorem leaf00445_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00445=true := by decide +kernel
#print axioms leaf00445_rectangular
def affine00445 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00445 (IntegerComputedClassCell.leftNumerator ![(15/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(15/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(15/64),0,(1/2)] ![(1/64),1,(1/4)]))
theorem leaf00445_transform : affine00445=(NestedInteger.clearedAll 3 raw00445 (IntegerComputedClassCell.leftNumerator ![(15/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(15/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(15/64),0,(1/2)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf00445_transform
theorem leaf00445_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00445=true := by decide +kernel
#print axioms leaf00445_sign
theorem leaf00445_log : RationalLog.accepts (2329237143/2147483648) (87235131/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00445_log
def leaf00445 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (6054107627/1000000000000) (2329237143/2147483648) (87235131/2147483648) 0 8 ![52,0,4] ![(15/64),0,(1/2)] ![(1/64),1,(1/4)] affine00445
theorem leaf00445_checked : FastNestedCellData.accepts 1 0 4 leaf00445=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (6054107627/1000000000000) (2329237143/2147483648) (87235131/2147483648) 0 8 ![52,0,4] ![(15/64),0,(1/2)] ![(1/64),1,(1/4)] 27919643497490511655293943808000000000000 30465972691845501494766108490205711302656 5032281315246842653259310563328000000000000 raw00445 affine00445
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00445_raw leaf00445_rectangular
    leaf00445_transform leaf00445_sign leaf00445_log
#print axioms leaf00445_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
