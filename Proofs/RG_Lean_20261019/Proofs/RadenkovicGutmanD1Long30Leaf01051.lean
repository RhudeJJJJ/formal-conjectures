/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01051 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 77531575851111720654900245299200000000000 69750217417112802918851920733790623760384 165953599634029486974962971443200000000000))
theorem leaf01051_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 77531575851111720654900245299200000000000 69750217417112802918851920733790623760384 165953599634029486974962971443200000000000 raw01051=true := by decide +kernel
#print axioms leaf01051_raw
theorem leaf01051_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01051=true := by decide +kernel
#print axioms leaf01051_rectangular
def affine01051 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01051 (IntegerComputedClassCell.leftNumerator ![(11/40),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/40),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/40),0,(1/16)] ![(3/160),1,(1/16)]))
theorem leaf01051_transform : affine01051=(NestedInteger.clearedAll 3 raw01051 (IntegerComputedClassCell.leftNumerator ![(11/40),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/40),0,(1/16)] ![(3/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/40),0,(1/16)] ![(3/160),1,(1/16)])) := by decide +kernel
#print axioms leaf01051_transform
theorem leaf01051_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01051=true := by decide +kernel
#print axioms leaf01051_sign
theorem leaf01051_log : RationalLog.accepts (2720488391/4294967296) (-245152727/1073741824) 1 8=true := by decide +kernel
#print axioms leaf01051_log
def leaf01051 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (42029951487/100000000000) (2720488391/4294967296) (-245152727/1073741824) 1 8 ![60,0,4] ![(11/40),0,(1/16)] ![(3/160),1,(1/16)] affine01051
theorem leaf01051_checked : FastNestedCellData.accepts 1 2 4 leaf01051=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (42029951487/100000000000) (2720488391/4294967296) (-245152727/1073741824) 1 8 ![60,0,4] ![(11/40),0,(1/16)] ![(3/160),1,(1/16)] 77531575851111720654900245299200000000000 69750217417112802918851920733790623760384 165953599634029486974962971443200000000000 raw01051 affine01051
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01051_raw leaf01051_rectangular
    leaf01051_transform leaf01051_sign leaf01051_log
#print axioms leaf01051_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
