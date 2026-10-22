/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01104 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3801461059436407216436525662208000000000000 4391838408005895697912334564775992330551296 21311574118184916415668648148992000000000000))
theorem leaf01104_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3801461059436407216436525662208000000000000 4391838408005895697912334564775992330551296 21311574118184916415668648148992000000000000 raw01104=true := by decide +kernel
#print axioms leaf01104_raw
theorem leaf01104_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01104=true := by decide +kernel
#print axioms leaf01104_rectangular
def affine01104 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01104 (IntegerComputedClassCell.leftNumerator ![(17/32),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/32),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/32),0,(15/16)] ![(1/32),1,(1/16)]))
theorem leaf01104_transform : affine01104=(NestedInteger.clearedAll 3 raw01104 (IntegerComputedClassCell.leftNumerator ![(17/32),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/32),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/32),0,(15/16)] ![(1/32),1,(1/16)])) := by decide +kernel
#print axioms leaf01104_transform
theorem leaf01104_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01104=true := by decide +kernel
#print axioms leaf01104_sign
theorem leaf01104_log : RationalLog.accepts (4114152729/4294967296) (-11545689/536870912) 1 8=true := by decide +kernel
#print axioms leaf01104_log
def leaf01104 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (206077616963/1000000000000) (4114152729/4294967296) (-11545689/536870912) 1 8 ![60,0,4] ![(17/32),0,(15/16)] ![(1/32),1,(1/16)] affine01104
theorem leaf01104_checked : FastNestedCellData.accepts 1 2 4 leaf01104=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (206077616963/1000000000000) (4114152729/4294967296) (-11545689/536870912) 1 8 ![60,0,4] ![(17/32),0,(15/16)] ![(1/32),1,(1/16)] 3801461059436407216436525662208000000000000 4391838408005895697912334564775992330551296 21311574118184916415668648148992000000000000 raw01104 affine01104
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01104_raw leaf01104_rectangular
    leaf01104_transform leaf01104_sign leaf01104_log
#print axioms leaf01104_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
