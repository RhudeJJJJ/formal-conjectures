/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01224 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 477782733051040562397545758720000000000 537114585441629487723026196214591782912 51843728385847130126165213184000000000000))
theorem leaf01224_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 477782733051040562397545758720000000000 537114585441629487723026196214591782912 51843728385847130126165213184000000000000 raw01224=true := by decide +kernel
#print axioms leaf01224_raw
theorem leaf01224_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01224=true := by decide +kernel
#print axioms leaf01224_rectangular
def affine01224 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01224 (IntegerComputedClassCell.leftNumerator ![(19/64),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/64),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/64),0,(15/16)] ![(1/64),1,(1/16)]))
theorem leaf01224_transform : affine01224=(NestedInteger.clearedAll 3 raw01224 (IntegerComputedClassCell.leftNumerator ![(19/64),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/64),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/64),0,(15/16)] ![(1/64),1,(1/16)])) := by decide +kernel
#print axioms leaf01224_transform
theorem leaf01224_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01224=true := by decide +kernel
#print axioms leaf01224_sign
theorem leaf01224_log : RationalLog.accepts (1194703425/1073741824) (14327527/268435456) 0 8=true := by decide +kernel
#print axioms leaf01224_log
def leaf01224 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (10360261543/1000000000000) (1194703425/1073741824) (14327527/268435456) 0 8 ![60,0,4] ![(19/64),0,(15/16)] ![(1/64),1,(1/16)] affine01224
theorem leaf01224_checked : FastNestedCellData.accepts 1 2 4 leaf01224=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (10360261543/1000000000000) (1194703425/1073741824) (14327527/268435456) 0 8 ![60,0,4] ![(19/64),0,(15/16)] ![(1/64),1,(1/16)] 477782733051040562397545758720000000000 537114585441629487723026196214591782912 51843728385847130126165213184000000000000 raw01224 affine01224
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01224_raw leaf01224_rectangular
    leaf01224_transform leaf01224_sign leaf01224_log
#print axioms leaf01224_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
