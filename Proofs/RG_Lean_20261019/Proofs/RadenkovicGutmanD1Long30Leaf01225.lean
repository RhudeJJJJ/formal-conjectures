/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01225 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 654773713926026389308309504000000000000 729976421873640319553948847914197450752 80333622969129393929446227968000000000000))
theorem leaf01225_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 654773713926026389308309504000000000000 729976421873640319553948847914197450752 80333622969129393929446227968000000000000 raw01225=true := by decide +kernel
#print axioms leaf01225_raw
theorem leaf01225_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01225=true := by decide +kernel
#print axioms leaf01225_rectangular
def affine01225 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01225 (IntegerComputedClassCell.leftNumerator ![(9/32),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/32),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/32),0,0] ![(1/64),1,(1/2)]))
theorem leaf01225_transform : affine01225=(NestedInteger.clearedAll 3 raw01225 (IntegerComputedClassCell.leftNumerator ![(9/32),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/32),0,0] ![(1/64),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/32),0,0] ![(1/64),1,(1/2)])) := by decide +kernel
#print axioms leaf01225_transform
theorem leaf01225_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01225=true := by decide +kernel
#print axioms leaf01225_sign
theorem leaf01225_log : RationalLog.accepts (2372569441/2147483648) (214054211/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01225_log
def leaf01225 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (1135851333/125000000000) (2372569441/2147483648) (214054211/4294967296) 0 8 ![60,0,4] ![(9/32),0,0] ![(1/64),1,(1/2)] affine01225
theorem leaf01225_checked : FastNestedCellData.accepts 1 2 4 leaf01225=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (1135851333/125000000000) (2372569441/2147483648) (214054211/4294967296) 0 8 ![60,0,4] ![(9/32),0,0] ![(1/64),1,(1/2)] 654773713926026389308309504000000000000 729976421873640319553948847914197450752 80333622969129393929446227968000000000000 raw01225 affine01225
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01225_raw leaf01225_rectangular
    leaf01225_transform leaf01225_sign leaf01225_log
#print axioms leaf01225_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
