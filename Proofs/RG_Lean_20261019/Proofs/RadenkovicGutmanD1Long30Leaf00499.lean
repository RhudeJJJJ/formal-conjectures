/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00499 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 224887149512015819647905431552000000000000 201151615671536835429529433490267052179456 4124949316087717252565997453312000000000000))
theorem leaf00499_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 224887149512015819647905431552000000000000 201151615671536835429529433490267052179456 4124949316087717252565997453312000000000000 raw00499=true := by decide +kernel
#print axioms leaf00499_raw
theorem leaf00499_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00499=true := by decide +kernel
#print axioms leaf00499_rectangular
def affine00499 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00499 (IntegerComputedClassCell.leftNumerator ![(21/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(21/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(21/1600),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00499_transform : affine00499=(NestedInteger.clearedAll 3 raw00499 (IntegerComputedClassCell.leftNumerator ![(21/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(21/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(21/1600),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00499_transform
theorem leaf00499_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00499=true := by decide +kernel
#print axioms leaf00499_sign
theorem leaf00499_log : RationalLog.accepts (1831516013/2147483648) (-341777887/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00499_log
def leaf00499 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (48764627213/1000000000000) (1831516013/2147483648) (-341777887/4294967296) 1 8 ![60,0,4] ![(21/1600),0,(1/2)] ![(1/3200),1,(1/2)] affine00499
theorem leaf00499_checked : FastNestedCellData.accepts 1 2 4 leaf00499=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (48764627213/1000000000000) (1831516013/2147483648) (-341777887/4294967296) 1 8 ![60,0,4] ![(21/1600),0,(1/2)] ![(1/3200),1,(1/2)] 224887149512015819647905431552000000000000 201151615671536835429529433490267052179456 4124949316087717252565997453312000000000000 raw00499 affine00499
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00499_raw leaf00499_rectangular
    leaf00499_transform leaf00499_sign leaf00499_log
#print axioms leaf00499_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
