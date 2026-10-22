/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01181 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 6858276851127979643197666099200000000000 8329626251989119230839208101902985199616 280053005724798537116938141696000000000000))
theorem leaf01181_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 6858276851127979643197666099200000000000 8329626251989119230839208101902985199616 280053005724798537116938141696000000000000 raw01181=true := by decide +kernel
#print axioms leaf01181_raw
theorem leaf01181_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01181=true := by decide +kernel
#print axioms leaf01181_rectangular
def affine01181 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01181 (IntegerComputedClassCell.leftNumerator ![(15/32),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(15/32),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(15/32),0,(1/2)] ![(1/32),1,(1/4)]))
theorem leaf01181_transform : affine01181=(NestedInteger.clearedAll 3 raw01181 (IntegerComputedClassCell.leftNumerator ![(15/32),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(15/32),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(15/32),0,(1/2)] ![(1/32),1,(1/4)])) := by decide +kernel
#print axioms leaf01181_transform
theorem leaf01181_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01181=true := by decide +kernel
#print axioms leaf01181_sign
theorem leaf01181_log : RationalLog.accepts (2532861865/2147483648) (354448779/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01181_log
def leaf01181 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (14871517323/500000000000) (2532861865/2147483648) (354448779/4294967296) 0 8 ![60,0,4] ![(15/32),0,(1/2)] ![(1/32),1,(1/4)] affine01181
theorem leaf01181_checked : FastNestedCellData.accepts 1 2 4 leaf01181=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (14871517323/500000000000) (2532861865/2147483648) (354448779/4294967296) 0 8 ![60,0,4] ![(15/32),0,(1/2)] ![(1/32),1,(1/4)] 6858276851127979643197666099200000000000 8329626251989119230839208101902985199616 280053005724798537116938141696000000000000 raw01181 affine01181
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01181_raw leaf01181_rectangular
    leaf01181_transform leaf01181_sign leaf01181_log
#print axioms leaf01181_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
