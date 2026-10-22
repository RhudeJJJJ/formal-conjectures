/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01158 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 3714496275696997578090940989440000000000 4760462171898823572471728028745646211072 59102917892356271286414999552000000000000))
theorem leaf01158_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 3714496275696997578090940989440000000000 4760462171898823572471728028745646211072 59102917892356271286414999552000000000000 raw01158=true := by decide +kernel
#print axioms leaf01158_raw
theorem leaf01158_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01158=true := by decide +kernel
#print axioms leaf01158_rectangular
def affine01158 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01158 (IntegerComputedClassCell.leftNumerator ![(13/16),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/16),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/16),0,(7/8)] ![(1/16),1,(1/16)]))
theorem leaf01158_transform : affine01158=(NestedInteger.clearedAll 3 raw01158 (IntegerComputedClassCell.leftNumerator ![(13/16),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/16),0,(7/8)] ![(1/16),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/16),0,(7/8)] ![(1/16),1,(1/16)])) := by decide +kernel
#print axioms leaf01158_transform
theorem leaf01158_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01158=true := by decide +kernel
#print axioms leaf01158_sign
theorem leaf01158_log : RationalLog.accepts (5094083675/4294967296) (183218861/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01158_log
def leaf01158 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (20136324659/250000000000) (5094083675/4294967296) (183218861/2147483648) 0 8 ![60,0,4] ![(13/16),0,(7/8)] ![(1/16),1,(1/16)] affine01158
theorem leaf01158_checked : FastNestedCellData.accepts 1 2 4 leaf01158=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (20136324659/250000000000) (5094083675/4294967296) (183218861/2147483648) 0 8 ![60,0,4] ![(13/16),0,(7/8)] ![(1/16),1,(1/16)] 3714496275696997578090940989440000000000 4760462171898823572471728028745646211072 59102917892356271286414999552000000000000 raw01158 affine01158
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01158_raw leaf01158_rectangular
    leaf01158_transform leaf01158_sign leaf01158_log
#print axioms leaf01158_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
