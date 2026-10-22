/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00731 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2930343027801373438716564996096000000000000 779346135820893933140308181272504112775168 1226511587203928670614251896832000000000000))
theorem leaf00731_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2930343027801373438716564996096000000000000 779346135820893933140308181272504112775168 1226511587203928670614251896832000000000000 raw00731=true := by decide +kernel
#print axioms leaf00731_raw
theorem leaf00731_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00731=true := by decide +kernel
#print axioms leaf00731_rectangular
def affine00731 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00731 (IntegerComputedClassCell.leftNumerator ![(203/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(203/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(203/6400),0,(1/16)] ![(3/6400),1,(1/16)]))
theorem leaf00731_transform : affine00731=(NestedInteger.clearedAll 3 raw00731 (IntegerComputedClassCell.leftNumerator ![(203/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(203/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(203/6400),0,(1/16)] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00731_transform
theorem leaf00731_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00731=true := by decide +kernel
#print axioms leaf00731_sign
theorem leaf00731_log : RationalLog.accepts (698462857/4294967296) (-243781977/268435456) 3 8=true := by decide +kernel
#print axioms leaf00731_log
def leaf00731 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (317708427687/500000000000) (698462857/4294967296) (-243781977/268435456) 3 8 ![60,0,4] ![(203/6400),0,(1/16)] ![(3/6400),1,(1/16)] affine00731
theorem leaf00731_checked : FastNestedCellData.accepts 1 2 4 leaf00731=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (317708427687/500000000000) (698462857/4294967296) (-243781977/268435456) 3 8 ![60,0,4] ![(203/6400),0,(1/16)] ![(3/6400),1,(1/16)] 2930343027801373438716564996096000000000000 779346135820893933140308181272504112775168 1226511587203928670614251896832000000000000 raw00731 affine00731
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00731_raw leaf00731_rectangular
    leaf00731_transform leaf00731_sign leaf00731_log
#print axioms leaf00731_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
