/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00589 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 79578253034402153274076561408000000000000 68254714033967542299543817271257694470144 988867241990506757389620871168000000000000))
theorem leaf00589_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 79578253034402153274076561408000000000000 68254714033967542299543817271257694470144 988867241990506757389620871168000000000000 raw00589=true := by decide +kernel
#print axioms leaf00589_raw
theorem leaf00589_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00589=true := by decide +kernel
#print axioms leaf00589_rectangular
def affine00589 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00589 (IntegerComputedClassCell.leftNumerator ![(3/160),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/160),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/160),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00589_transform : affine00589=(NestedInteger.clearedAll 3 raw00589 (IntegerComputedClassCell.leftNumerator ![(3/160),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/160),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/160),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00589_transform
theorem leaf00589_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00589=true := by decide +kernel
#print axioms leaf00589_sign
theorem leaf00589_log : RationalLog.accepts (1722983083/2147483648) (-472961021/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00589_log
def leaf00589 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (34511565929/500000000000) (1722983083/2147483648) (-472961021/4294967296) 1 8 ![60,0,4] ![(3/160),0,(1/2)] ![(1/3200),1,(1/2)] affine00589
theorem leaf00589_checked : FastNestedCellData.accepts 1 2 4 leaf00589=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (34511565929/500000000000) (1722983083/2147483648) (-472961021/4294967296) 1 8 ![60,0,4] ![(3/160),0,(1/2)] ![(1/3200),1,(1/2)] 79578253034402153274076561408000000000000 68254714033967542299543817271257694470144 988867241990506757389620871168000000000000 raw00589 affine00589
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00589_raw leaf00589_rectangular
    leaf00589_transform leaf00589_sign leaf00589_log
#print axioms leaf00589_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
