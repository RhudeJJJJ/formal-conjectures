/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01199 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 5382051488490275906107998208000000000000 6294076622951579293175795539495507460096 337072968632991739168296009728000000000000))
theorem leaf01199_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 5382051488490275906107998208000000000000 6294076622951579293175795539495507460096 337072968632991739168296009728000000000000 raw01199=true := by decide +kernel
#print axioms leaf01199_raw
theorem leaf01199_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01199=true := by decide +kernel
#print axioms leaf01199_rectangular
def affine01199 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01199 (IntegerComputedClassCell.leftNumerator ![(3/8),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/8),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/8),0,(15/16)] ![(1/32),1,(1/16)]))
theorem leaf01199_transform : affine01199=(NestedInteger.clearedAll 3 raw01199 (IntegerComputedClassCell.leftNumerator ![(3/8),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/8),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/8),0,(15/16)] ![(1/32),1,(1/16)])) := by decide +kernel
#print axioms leaf01199_transform
theorem leaf01199_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01199=true := by decide +kernel
#print axioms leaf01199_sign
theorem leaf01199_log : RationalLog.accepts (2465354393/2147483648) (18527255/268435456) 0 8=true := by decide +kernel
#print axioms leaf01199_log
def leaf01199 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (4668185533/250000000000) (2465354393/2147483648) (18527255/268435456) 0 8 ![60,0,4] ![(3/8),0,(15/16)] ![(1/32),1,(1/16)] affine01199
theorem leaf01199_checked : FastNestedCellData.accepts 1 2 4 leaf01199=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (4668185533/250000000000) (2465354393/2147483648) (18527255/268435456) 0 8 ![60,0,4] ![(3/8),0,(15/16)] ![(1/32),1,(1/16)] 5382051488490275906107998208000000000000 6294076622951579293175795539495507460096 337072968632991739168296009728000000000000 raw01199 affine01199
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01199_raw leaf01199_rectangular
    leaf01199_transform leaf01199_sign leaf01199_log
#print axioms leaf01199_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
