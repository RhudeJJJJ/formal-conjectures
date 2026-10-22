/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01203 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 11956491698113910682510971371520000000000 13871232372299855180244682137925431853056 856033960527516114043998830592000000000000))
theorem leaf01203_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 11956491698113910682510971371520000000000 13871232372299855180244682137925431853056 856033960527516114043998830592000000000000 raw01203=true := by decide +kernel
#print axioms leaf01203_raw
theorem leaf01203_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01203=true := by decide +kernel
#print axioms leaf01203_rectangular
def affine01203 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01203 (IntegerComputedClassCell.leftNumerator ![(23/64),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/64),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/64),0,(7/8)] ![(1/64),1,(1/16)]))
theorem leaf01203_transform : affine01203=(NestedInteger.clearedAll 3 raw01203 (IntegerComputedClassCell.leftNumerator ![(23/64),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/64),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/64),0,(7/8)] ![(1/64),1,(1/16)])) := by decide +kernel
#print axioms leaf01203_transform
theorem leaf01203_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01203=true := by decide +kernel
#print axioms leaf01203_sign
theorem leaf01203_log : RationalLog.accepts (4903319725/4294967296) (284474001/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01203_log
def leaf01203 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (16204067843/1000000000000) (4903319725/4294967296) (284474001/4294967296) 0 8 ![60,0,4] ![(23/64),0,(7/8)] ![(1/64),1,(1/16)] affine01203
theorem leaf01203_checked : FastNestedCellData.accepts 1 2 4 leaf01203=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (16204067843/1000000000000) (4903319725/4294967296) (284474001/4294967296) 0 8 ![60,0,4] ![(23/64),0,(7/8)] ![(1/64),1,(1/16)] 11956491698113910682510971371520000000000 13871232372299855180244682137925431853056 856033960527516114043998830592000000000000 raw01203 affine01203
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01203_raw leaf01203_rectangular
    leaf01203_transform leaf01203_sign leaf01203_log
#print axioms leaf01203_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
