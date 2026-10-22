/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01157 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 72576047101171097201645977600000000000 93021762289090044347009689179226374144 1154465669364714748036251648000000000000))
theorem leaf01157_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 72576047101171097201645977600000000000 93021762289090044347009689179226374144 1154465669364714748036251648000000000000 raw01157=true := by decide +kernel
#print axioms leaf01157_raw
theorem leaf01157_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01157=true := by decide +kernel
#print axioms leaf01157_rectangular
def affine01157 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01157 (IntegerComputedClassCell.leftNumerator ![(13/16),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(13/16),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.denominator ![(13/16),0,(3/4)] ![(1/16),1,(1/8)]))
theorem leaf01157_transform : affine01157=(NestedInteger.clearedAll 3 raw01157 (IntegerComputedClassCell.leftNumerator ![(13/16),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(13/16),0,(3/4)] ![(1/16),1,(1/8)]) (IntegerComputedClassCell.denominator ![(13/16),0,(3/4)] ![(1/16),1,(1/8)])) := by decide +kernel
#print axioms leaf01157_transform
theorem leaf01157_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01157=true := by decide +kernel
#print axioms leaf01157_sign
theorem leaf01157_log : RationalLog.accepts (5094434205/4294967296) (22911593/268435456) 0 8=true := by decide +kernel
#print axioms leaf01157_log
def leaf01157 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (1258993727/15625000000) (5094434205/4294967296) (22911593/268435456) 0 8 ![60,0,4] ![(13/16),0,(3/4)] ![(1/16),1,(1/8)] affine01157
theorem leaf01157_checked : FastNestedCellData.accepts 1 2 4 leaf01157=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (1258993727/15625000000) (5094434205/4294967296) (22911593/268435456) 0 8 ![60,0,4] ![(13/16),0,(3/4)] ![(1/16),1,(1/8)] 72576047101171097201645977600000000000 93021762289090044347009689179226374144 1154465669364714748036251648000000000000 raw01157 affine01157
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01157_raw leaf01157_rectangular
    leaf01157_transform leaf01157_sign leaf01157_log
#print axioms leaf01157_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
