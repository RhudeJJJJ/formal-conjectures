/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01201 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 74728378904888451648930709504000000000000 86695590487170030197015593464878707245056 5350214314401971047778175942656000000000000))
theorem leaf01201_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 74728378904888451648930709504000000000000 86695590487170030197015593464878707245056 5350214314401971047778175942656000000000000 raw01201=true := by decide +kernel
#print axioms leaf01201_raw
theorem leaf01201_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01201=true := by decide +kernel
#print axioms leaf01201_rectangular
def affine01201 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01201 (IntegerComputedClassCell.leftNumerator ![(23/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/64),0,(1/2)] ![(1/64),1,(1/4)]))
theorem leaf01201_transform : affine01201=(NestedInteger.clearedAll 3 raw01201 (IntegerComputedClassCell.leftNumerator ![(23/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/64),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/64),0,(1/2)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf01201_transform
theorem leaf01201_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01201=true := by decide +kernel
#print axioms leaf01201_sign
theorem leaf01201_log : RationalLog.accepts (2451660647/2147483648) (4444917/67108864) 0 8=true := by decide +kernel
#print axioms leaf01201_log
def leaf01201 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (16204134151/1000000000000) (2451660647/2147483648) (4444917/67108864) 0 8 ![60,0,4] ![(23/64),0,(1/2)] ![(1/64),1,(1/4)] affine01201
theorem leaf01201_checked : FastNestedCellData.accepts 1 2 4 leaf01201=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (16204134151/1000000000000) (2451660647/2147483648) (4444917/67108864) 0 8 ![60,0,4] ![(23/64),0,(1/2)] ![(1/64),1,(1/4)] 74728378904888451648930709504000000000000 86695590487170030197015593464878707245056 5350214314401971047778175942656000000000000 raw01201 affine01201
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01201_raw leaf01201_rectangular
    leaf01201_transform leaf01201_sign leaf01201_log
#print axioms leaf01201_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
