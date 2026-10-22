/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00114 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 43381037076997297923948544000000000000 42388196446411496007238025989362548736 4400527939941533332247937024000000000000))
theorem leaf00114_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 43381037076997297923948544000000000000 42388196446411496007238025989362548736 4400527939941533332247937024000000000000 raw00114=true := by decide +kernel
#print axioms leaf00114_raw
theorem leaf00114_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00114=true := by decide +kernel
#print axioms leaf00114_rectangular
def affine00114 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00114 (IntegerComputedClassCell.leftNumerator ![(41/16000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(41/16000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(41/16000),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00114_transform : affine00114=(NestedInteger.clearedAll 3 raw00114 (IntegerComputedClassCell.leftNumerator ![(41/16000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(41/16000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(41/16000),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00114_transform
theorem leaf00114_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00114=true := by decide +kernel
#print axioms leaf00114_sign
theorem leaf00114_log : RationalLog.accepts (64947369/67108864) (-35153147/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00114_log
def leaf00114 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (9632525239/1000000000000) (64947369/67108864) (-35153147/2147483648) 1 8 ![60,0,4] ![(41/16000),0,(1/2)] ![(3/32000),1,(1/2)] affine00114
theorem leaf00114_checked : FastNestedCellData.accepts 1 2 4 leaf00114=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (9632525239/1000000000000) (64947369/67108864) (-35153147/2147483648) 1 8 ![60,0,4] ![(41/16000),0,(1/2)] ![(3/32000),1,(1/2)] 43381037076997297923948544000000000000 42388196446411496007238025989362548736 4400527939941533332247937024000000000000 raw00114 affine00114
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00114_raw leaf00114_rectangular
    leaf00114_transform leaf00114_sign leaf00114_log
#print axioms leaf00114_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
