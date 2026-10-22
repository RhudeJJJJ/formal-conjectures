/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01000 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3061241484290029337636887330816000000000000 1589377555521286539960928862497087135154176 2394358722895636254667250335744000000000000))
theorem leaf01000_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3061241484290029337636887330816000000000000 1589377555521286539960928862497087135154176 2394358722895636254667250335744000000000000 raw01000=true := by decide +kernel
#print axioms leaf01000_raw
theorem leaf01000_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01000=true := by decide +kernel
#print axioms leaf01000_rectangular
def affine01000 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01000 (IntegerComputedClassCell.leftNumerator ![(3/20),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/20),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/20),0,0] ![(1/160),1,(1/16)]))
theorem leaf01000_transform : affine01000=(NestedInteger.clearedAll 3 raw01000 (IntegerComputedClassCell.leftNumerator ![(3/20),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/20),0,0] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/20),0,0] ![(1/160),1,(1/16)])) := by decide +kernel
#print axioms leaf01000_transform
theorem leaf01000_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01000=true := by decide +kernel
#print axioms leaf01000_sign
theorem leaf01000_log : RationalLog.accepts (1340256689/4294967296) (-1250461281/2147483648) 2 8=true := by decide +kernel
#print axioms leaf01000_log
def leaf01000 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (331900466777/500000000000) (1340256689/4294967296) (-1250461281/2147483648) 2 8 ![60,0,4] ![(3/20),0,0] ![(1/160),1,(1/16)] affine01000
theorem leaf01000_checked : FastNestedCellData.accepts 1 2 4 leaf01000=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (331900466777/500000000000) (1340256689/4294967296) (-1250461281/2147483648) 2 8 ![60,0,4] ![(3/20),0,0] ![(1/160),1,(1/16)] 3061241484290029337636887330816000000000000 1589377555521286539960928862497087135154176 2394358722895636254667250335744000000000000 raw01000 affine01000
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01000_raw leaf01000_rectangular
    leaf01000_transform leaf01000_sign leaf01000_log
#print axioms leaf01000_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
