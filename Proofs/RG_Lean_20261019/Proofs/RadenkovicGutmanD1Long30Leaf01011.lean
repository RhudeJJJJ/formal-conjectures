/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01011 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 10912122735871180331209487024128000000000000 6569016280158482486119654252817137807654912 11104801977508252921409006731264000000000000))
theorem leaf01011_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 10912122735871180331209487024128000000000000 6569016280158482486119654252817137807654912 11104801977508252921409006731264000000000000 raw01011=true := by decide +kernel
#print axioms leaf01011_raw
theorem leaf01011_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01011=true := by decide +kernel
#print axioms leaf01011_rectangular
def affine01011 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01011 (IntegerComputedClassCell.leftNumerator ![(13/80),0,(1/16)] ![(1/80),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/80),0,(1/16)] ![(1/80),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/80),0,(1/16)] ![(1/80),1,(1/16)]))
theorem leaf01011_transform : affine01011=(NestedInteger.clearedAll 3 raw01011 (IntegerComputedClassCell.leftNumerator ![(13/80),0,(1/16)] ![(1/80),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/80),0,(1/16)] ![(1/80),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/80),0,(1/16)] ![(1/80),1,(1/16)])) := by decide +kernel
#print axioms leaf01011_transform
theorem leaf01011_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01011=true := by decide +kernel
#print axioms leaf01011_sign
theorem leaf01011_log : RationalLog.accepts (1624543673/4294967296) (-2087820141/4294967296) 2 8=true := by decide +kernel
#print axioms leaf01011_log
def leaf01011 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (591547358833/1000000000000) (1624543673/4294967296) (-2087820141/4294967296) 2 8 ![60,0,4] ![(13/80),0,(1/16)] ![(1/80),1,(1/16)] affine01011
theorem leaf01011_checked : FastNestedCellData.accepts 1 2 4 leaf01011=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (591547358833/1000000000000) (1624543673/4294967296) (-2087820141/4294967296) 2 8 ![60,0,4] ![(13/80),0,(1/16)] ![(1/80),1,(1/16)] 10912122735871180331209487024128000000000000 6569016280158482486119654252817137807654912 11104801977508252921409006731264000000000000 raw01011 affine01011
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01011_raw leaf01011_rectangular
    leaf01011_transform leaf01011_sign leaf01011_log
#print axioms leaf01011_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
