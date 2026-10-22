/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01065 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 21159752406896438484493192396800000000000 21079746434916550417181439766306140192768 57428112836882294641459724288000000000000))
theorem leaf01065_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 21159752406896438484493192396800000000000 21079746434916550417181439766306140192768 57428112836882294641459724288000000000000 raw01065=true := by decide +kernel
#print axioms leaf01065_raw
theorem leaf01065_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01065=true := by decide +kernel
#print axioms leaf01065_rectangular
def affine01065 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01065 (IntegerComputedClassCell.leftNumerator ![(53/160),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(53/160),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(53/160),0,0] ![(3/160),1,(1/16)]))
theorem leaf01065_transform : affine01065=(NestedInteger.clearedAll 3 raw01065 (IntegerComputedClassCell.leftNumerator ![(53/160),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(53/160),0,0] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(53/160),0,0] ![(3/160),1,(1/16)])) := by decide +kernel
#print axioms leaf01065_transform
theorem leaf01065_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01065=true := by decide +kernel
#print axioms leaf01065_sign
theorem leaf01065_log : RationalLog.accepts (391233545/536870912) (-679577667/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01065_log
def leaf01065 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (367063192461/1000000000000) (391233545/536870912) (-679577667/4294967296) 1 8 ![60,0,4] ![(53/160),0,0] ![(3/160),1,(1/16)] affine01065
theorem leaf01065_checked : FastNestedCellData.accepts 1 2 4 leaf01065=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (367063192461/1000000000000) (391233545/536870912) (-679577667/4294967296) 1 8 ![60,0,4] ![(53/160),0,0] ![(3/160),1,(1/16)] 21159752406896438484493192396800000000000 21079746434916550417181439766306140192768 57428112836882294641459724288000000000000 raw01065 affine01065
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01065_raw leaf01065_rectangular
    leaf01065_transform leaf01065_sign leaf01065_log
#print axioms leaf01065_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
