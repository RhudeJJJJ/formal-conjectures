/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01340 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 607311672776419682400862208000000000000 611925146384485248455703918677669707776 4646718922763696278721148223488000000000000))
theorem leaf01340_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 607311672776419682400862208000000000000 611925146384485248455703918677669707776 4646718922763696278721148223488000000000000 raw01340=true := by decide +kernel
#print axioms leaf01340_raw
theorem leaf01340_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01340=true := by decide +kernel
#print axioms leaf01340_rectangular
def affine01340 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01340 (IntegerComputedClassCell.leftNumerator ![(1/16),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/16),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(1/16),0,0] ![(1/256),1,1]))
theorem leaf01340_transform : affine01340=(NestedInteger.clearedAll 3 raw01340 (IntegerComputedClassCell.leftNumerator ![(1/16),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/16),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(1/16),0,0] ![(1/256),1,1])) := by decide +kernel
#print axioms leaf01340_transform
theorem leaf01340_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01340=true := by decide +kernel
#print axioms leaf01340_sign
theorem leaf01340_log : RationalLog.accepts (2163512203/2147483648) (15969033/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01340_log
def leaf01340 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (131689727/1000000000000) (2163512203/2147483648) (15969033/4294967296) 0 8 ![60,0,4] ![(1/16),0,0] ![(1/256),1,1] affine01340
theorem leaf01340_checked : FastNestedCellData.accepts 1 2 4 leaf01340=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (131689727/1000000000000) (2163512203/2147483648) (15969033/4294967296) 0 8 ![60,0,4] ![(1/16),0,0] ![(1/256),1,1] 607311672776419682400862208000000000000 611925146384485248455703918677669707776 4646718922763696278721148223488000000000000 raw01340 affine01340
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01340_raw leaf01340_rectangular
    leaf01340_transform leaf01340_sign leaf01340_log
#print axioms leaf01340_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
