/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01290 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 1865884354955991429542838272000000000000 1939500189603578038355088526248222130176 1198408395913562617926603767808000000000000))
theorem leaf01290_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 1865884354955991429542838272000000000000 1939500189603578038355088526248222130176 1198408395913562617926603767808000000000000 raw01290=true := by decide +kernel
#print axioms leaf01290_raw
theorem leaf01290_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01290=true := by decide +kernel
#print axioms leaf01290_rectangular
def affine01290 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01290 (IntegerComputedClassCell.leftNumerator ![(19/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/128),0,0] ![(1/128),1,(1/2)]))
theorem leaf01290_transform : affine01290=(NestedInteger.clearedAll 3 raw01290 (IntegerComputedClassCell.leftNumerator ![(19/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/128),0,0] ![(1/128),1,(1/2)])) := by decide +kernel
#print axioms leaf01290_transform
theorem leaf01290_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01290=true := by decide +kernel
#print axioms leaf01290_sign
theorem leaf01290_log : RationalLog.accepts (1114301411/1073741824) (79624595/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01290_log
def leaf01290 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (1618396697/1000000000000) (1114301411/1073741824) (79624595/4294967296) 0 8 ![60,0,4] ![(19/128),0,0] ![(1/128),1,(1/2)] affine01290
theorem leaf01290_checked : FastNestedCellData.accepts 1 2 4 leaf01290=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (1618396697/1000000000000) (1114301411/1073741824) (79624595/4294967296) 0 8 ![60,0,4] ![(19/128),0,0] ![(1/128),1,(1/2)] 1865884354955991429542838272000000000000 1939500189603578038355088526248222130176 1198408395913562617926603767808000000000000 raw01290 affine01290
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01290_raw leaf01290_rectangular
    leaf01290_transform leaf01290_sign leaf01290_log
#print axioms leaf01290_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
