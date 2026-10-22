/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00546 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 126482570118243732298051616768000000000000 48989575386959857804690996553022147919872 111638178510252948985139429376000000000000))
theorem leaf00546_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 126482570118243732298051616768000000000000 48989575386959857804690996553022147919872 111638178510252948985139429376000000000000 raw00546=true := by decide +kernel
#print axioms leaf00546_raw
theorem leaf00546_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00546=true := by decide +kernel
#print axioms leaf00546_rectangular
def affine00546 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00546 (IntegerComputedClassCell.leftNumerator ![(13/800),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/800),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/800),0,(1/16)] ![(1/3200),1,(1/16)]))
theorem leaf00546_transform : affine00546=(NestedInteger.clearedAll 3 raw00546 (IntegerComputedClassCell.leftNumerator ![(13/800),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/800),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/800),0,(1/16)] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00546_transform
theorem leaf00546_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00546=true := by decide +kernel
#print axioms leaf00546_sign
theorem leaf00546_log : RationalLog.accepts (578089411/2147483648) (-88068541/134217728) 2 8=true := by decide +kernel
#print axioms leaf00546_log
def leaf00546 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (109706141843/250000000000) (578089411/2147483648) (-88068541/134217728) 2 8 ![60,0,4] ![(13/800),0,(1/16)] ![(1/3200),1,(1/16)] affine00546
theorem leaf00546_checked : FastNestedCellData.accepts 1 2 4 leaf00546=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (109706141843/250000000000) (578089411/2147483648) (-88068541/134217728) 2 8 ![60,0,4] ![(13/800),0,(1/16)] ![(1/3200),1,(1/16)] 126482570118243732298051616768000000000000 48989575386959857804690996553022147919872 111638178510252948985139429376000000000000 raw00546 affine00546
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00546_raw leaf00546_rectangular
    leaf00546_transform leaf00546_sign leaf00546_log
#print axioms leaf00546_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
