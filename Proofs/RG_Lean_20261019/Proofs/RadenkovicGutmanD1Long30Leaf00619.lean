/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00619 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1388460682609654403226927104000000000000 1170606922552442786779518636667158134784 15187883866601746051067019264000000000000))
theorem leaf00619_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1388460682609654403226927104000000000000 1170606922552442786779518636667158134784 15187883866601746051067019264000000000000 raw00619=true := by decide +kernel
#print axioms leaf00619_raw
theorem leaf00619_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00619=true := by decide +kernel
#print axioms leaf00619_rectangular
def affine00619 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00619 (IntegerComputedClassCell.leftNumerator ![(67/3200),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(67/3200),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(67/3200),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00619_transform : affine00619=(NestedInteger.clearedAll 3 raw00619 (IntegerComputedClassCell.leftNumerator ![(67/3200),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(67/3200),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(67/3200),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00619_transform
theorem leaf00619_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00619=true := by decide +kernel
#print axioms leaf00619_sign
theorem leaf00619_log : RationalLog.accepts (105060973/134217728) (-525966971/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00619_log
def leaf00619 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (77075050931/1000000000000) (105060973/134217728) (-525966971/4294967296) 1 8 ![60,0,4] ![(67/3200),0,(1/2)] ![(3/6400),1,(1/2)] affine00619
theorem leaf00619_checked : FastNestedCellData.accepts 1 2 4 leaf00619=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (77075050931/1000000000000) (105060973/134217728) (-525966971/4294967296) 1 8 ![60,0,4] ![(67/3200),0,(1/2)] ![(3/6400),1,(1/2)] 1388460682609654403226927104000000000000 1170606922552442786779518636667158134784 15187883866601746051067019264000000000000 raw00619 affine00619
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00619_raw leaf00619_rectangular
    leaf00619_transform leaf00619_sign leaf00619_log
#print axioms leaf00619_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
