/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00493 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 57086965946683258358988800000000000 57130318591863452627840223997329408 11537970494195896525973461401600000000000))
theorem leaf00493_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 57086965946683258358988800000000000 57130318591863452627840223997329408 11537970494195896525973461401600000000000 raw00493=true := by decide +kernel
#print axioms leaf00493_raw
theorem leaf00493_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00493=true := by decide +kernel
#print axioms leaf00493_rectangular
def affine00493 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00493 (IntegerComputedClassCell.leftNumerator ![(5/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(5/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(5/256),0,0] ![(1/256),1,1]))
theorem leaf00493_transform : affine00493=(NestedInteger.clearedAll 3 raw00493 (IntegerComputedClassCell.leftNumerator ![(5/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(5/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(5/256),0,0] ![(1/256),1,1])) := by decide +kernel
#print axioms leaf00493_transform
theorem leaf00493_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00493=true := by decide +kernel
#print axioms leaf00493_sign
theorem leaf00493_log : RationalLog.accepts (537275959/536870912) (1619577/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00493_log
def leaf00493 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (990301/200000000000) (537275959/536870912) (1619577/4294967296) 0 8 ![52,0,4] ![(5/256),0,0] ![(1/256),1,1] affine00493
theorem leaf00493_checked : FastNestedCellData.accepts 1 0 4 leaf00493=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (990301/200000000000) (537275959/536870912) (1619577/4294967296) 0 8 ![52,0,4] ![(5/256),0,0] ![(1/256),1,1] 57086965946683258358988800000000000 57130318591863452627840223997329408 11537970494195896525973461401600000000000 raw00493 affine00493
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00493_raw leaf00493_rectangular
    leaf00493_transform leaf00493_sign leaf00493_log
#print axioms leaf00493_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
