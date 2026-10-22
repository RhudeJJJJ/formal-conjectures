/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00089 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 9111183667529564707750936576000000000000 8938187347463647009309755953595151286272 1131030696024790882753101955072000000000000))
theorem leaf00089_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 9111183667529564707750936576000000000000 8938187347463647009309755953595151286272 1131030696024790882753101955072000000000000 raw00089=true := by decide +kernel
#print axioms leaf00089_raw
theorem leaf00089_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00089=true := by decide +kernel
#print axioms leaf00089_rectangular
def affine00089 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00089 (IntegerComputedClassCell.leftNumerator ![(67/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(67/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(67/32000),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00089_transform : affine00089=(NestedInteger.clearedAll 3 raw00089 (IntegerComputedClassCell.leftNumerator ![(67/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(67/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(67/32000),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00089_transform
theorem leaf00089_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00089=true := by decide +kernel
#print axioms leaf00089_sign
theorem leaf00089_log : RationalLog.accepts (1045095353/1073741824) (-7258889/536870912) 1 8=true := by decide +kernel
#print axioms leaf00089_log
def leaf00089 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (7902692101/1000000000000) (1045095353/1073741824) (-7258889/536870912) 1 8 ![60,0,4] ![(67/32000),0,(1/2)] ![(3/32000),1,(1/2)] affine00089
theorem leaf00089_checked : FastNestedCellData.accepts 1 2 4 leaf00089=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (7902692101/1000000000000) (1045095353/1073741824) (-7258889/536870912) 1 8 ![60,0,4] ![(67/32000),0,(1/2)] ![(3/32000),1,(1/2)] 9111183667529564707750936576000000000000 8938187347463647009309755953595151286272 1131030696024790882753101955072000000000000 raw00089 affine00089
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00089_raw leaf00089_rectangular
    leaf00089_transform leaf00089_sign leaf00089_log
#print axioms leaf00089_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
