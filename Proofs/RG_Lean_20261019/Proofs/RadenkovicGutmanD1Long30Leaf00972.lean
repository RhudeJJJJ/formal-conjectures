/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00972 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3646408705967481132337567105024000000000000 1752438985290020412149038622537787849572352 2955126177850212366286067859456000000000000))
theorem leaf00972_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3646408705967481132337567105024000000000000 1752438985290020412149038622537787849572352 2955126177850212366286067859456000000000000 raw00972=true := by decide +kernel
#print axioms leaf00972_raw
theorem leaf00972_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00972=true := by decide +kernel
#print axioms leaf00972_rectangular
def affine00972 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00972 (IntegerComputedClassCell.leftNumerator ![(9/80),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(9/80),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(9/80),0,(1/8)] ![(1/160),1,(1/8)]))
theorem leaf00972_transform : affine00972=(NestedInteger.clearedAll 3 raw00972 (IntegerComputedClassCell.leftNumerator ![(9/80),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(9/80),0,(1/8)] ![(1/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(9/80),0,(1/8)] ![(1/160),1,(1/8)])) := by decide +kernel
#print axioms leaf00972_transform
theorem leaf00972_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00972=true := by decide +kernel
#print axioms leaf00972_sign
theorem leaf00972_log : RationalLog.accepts (1295737749/4294967296) (-2573466559/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00972_log
def leaf00972 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (593016636117/1000000000000) (1295737749/4294967296) (-2573466559/4294967296) 2 8 ![60,0,4] ![(9/80),0,(1/8)] ![(1/160),1,(1/8)] affine00972
theorem leaf00972_checked : FastNestedCellData.accepts 1 2 4 leaf00972=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (593016636117/1000000000000) (1295737749/4294967296) (-2573466559/4294967296) 2 8 ![60,0,4] ![(9/80),0,(1/8)] ![(1/160),1,(1/8)] 3646408705967481132337567105024000000000000 1752438985290020412149038622537787849572352 2955126177850212366286067859456000000000000 raw00972 affine00972
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00972_raw leaf00972_rectangular
    leaf00972_transform leaf00972_sign leaf00972_log
#print axioms leaf00972_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
