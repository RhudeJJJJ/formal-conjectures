/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01234 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 2275533327741035441912020992000000000000 2515546724995792978247397157555094421504 318631667545173523505377968128000000000000))
theorem leaf01234_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 2275533327741035441912020992000000000000 2515546724995792978247397157555094421504 318631667545173523505377968128000000000000 raw01234=true := by decide +kernel
#print axioms leaf01234_raw
theorem leaf01234_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01234=true := by decide +kernel
#print axioms leaf01234_rectangular
def affine01234 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01234 (IntegerComputedClassCell.leftNumerator ![(17/64),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/64),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/64),0,(15/16)] ![(1/64),1,(1/16)]))
theorem leaf01234_transform : affine01234=(NestedInteger.clearedAll 3 raw01234 (IntegerComputedClassCell.leftNumerator ![(17/64),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/64),0,(15/16)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/64),0,(15/16)] ![(1/64),1,(1/16)])) := by decide +kernel
#print axioms leaf01234_transform
theorem leaf01234_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01234=true := by decide +kernel
#print axioms leaf01234_sign
theorem leaf01234_log : RationalLog.accepts (4710790889/4294967296) (198452979/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01234_log
def leaf01234 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (986855271/125000000000) (4710790889/4294967296) (198452979/4294967296) 0 8 ![60,0,4] ![(17/64),0,(15/16)] ![(1/64),1,(1/16)] affine01234
theorem leaf01234_checked : FastNestedCellData.accepts 1 2 4 leaf01234=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (986855271/125000000000) (4710790889/4294967296) (198452979/4294967296) 0 8 ![60,0,4] ![(17/64),0,(15/16)] ![(1/64),1,(1/16)] 2275533327741035441912020992000000000000 2515546724995792978247397157555094421504 318631667545173523505377968128000000000000 raw01234 affine01234
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01234_raw leaf01234_rectangular
    leaf01234_transform leaf01234_sign leaf01234_log
#print axioms leaf01234_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
