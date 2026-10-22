/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00984 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1145004166647685336066215116800000000000 775101556402261337578221106495513165824 2438941050010420804765876224000000000000))
theorem leaf00984_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1145004166647685336066215116800000000000 775101556402261337578221106495513165824 2438941050010420804765876224000000000000 raw00984=true := by decide +kernel
#print axioms leaf00984_raw
theorem leaf00984_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00984=true := by decide +kernel
#print axioms leaf00984_rectangular
def affine00984 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00984 (IntegerComputedClassCell.leftNumerator ![(1/8),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/8),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/8),0,(1/2)] ![(1/160),1,(1/2)]))
theorem leaf00984_transform : affine00984=(NestedInteger.clearedAll 3 raw00984 (IntegerComputedClassCell.leftNumerator ![(1/8),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/8),0,(1/2)] ![(1/160),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/8),0,(1/2)] ![(1/160),1,(1/2)])) := by decide +kernel
#print axioms leaf00984_transform
theorem leaf00984_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00984=true := by decide +kernel
#print axioms leaf00984_sign
theorem leaf00984_log : RationalLog.accepts (275785285/536870912) (-715257101/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00984_log
def leaf00984 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (79450624319/250000000000) (275785285/536870912) (-715257101/2147483648) 1 8 ![60,0,4] ![(1/8),0,(1/2)] ![(1/160),1,(1/2)] affine00984
theorem leaf00984_checked : FastNestedCellData.accepts 1 2 4 leaf00984=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (79450624319/250000000000) (275785285/536870912) (-715257101/2147483648) 1 8 ![60,0,4] ![(1/8),0,(1/2)] ![(1/160),1,(1/2)] 1145004166647685336066215116800000000000 775101556402261337578221106495513165824 2438941050010420804765876224000000000000 raw00984 affine00984
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00984_raw leaf00984_rectangular
    leaf00984_transform leaf00984_sign leaf00984_log
#print axioms leaf00984_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
