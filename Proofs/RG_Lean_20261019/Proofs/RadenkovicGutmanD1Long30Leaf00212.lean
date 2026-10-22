/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00212 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 5007241568924344505132384256000000000000 4272986315667391328675279893067364040704 61491164152107321539977805824000000000000))
theorem leaf00212_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 5007241568924344505132384256000000000000 4272986315667391328675279893067364040704 61491164152107321539977805824000000000000 raw00212=true := by decide +kernel
#print axioms leaf00212_raw
theorem leaf00212_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00212=true := by decide +kernel
#print axioms leaf00212_rectangular
def affine00212 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00212 (IntegerComputedClassCell.leftNumerator ![(71/16000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(71/16000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(71/16000),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00212_transform : affine00212=(NestedInteger.clearedAll 3 raw00212 (IntegerComputedClassCell.leftNumerator ![(71/16000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(71/16000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(71/16000),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00212_transform
theorem leaf00212_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00212=true := by decide +kernel
#print axioms leaf00212_sign
theorem leaf00212_log : RationalLog.accepts (856754371/1073741824) (-30300137/268435456) 1 8=true := by decide +kernel
#print axioms leaf00212_log
def leaf00212 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (17372358999/250000000000) (856754371/1073741824) (-30300137/268435456) 1 8 ![60,0,4] ![(71/16000),0,(1/8)] ![(3/32000),1,(1/8)] affine00212
theorem leaf00212_checked : FastNestedCellData.accepts 1 2 4 leaf00212=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (17372358999/250000000000) (856754371/1073741824) (-30300137/268435456) 1 8 ![60,0,4] ![(71/16000),0,(1/8)] ![(3/32000),1,(1/8)] 5007241568924344505132384256000000000000 4272986315667391328675279893067364040704 61491164152107321539977805824000000000000 raw00212 affine00212
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00212_raw leaf00212_rectangular
    leaf00212_transform leaf00212_sign leaf00212_log
#print axioms leaf00212_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
