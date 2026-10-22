/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00528 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 696974200676675950417367007232000000000000 542519511225286362650769676397360512499712 4786269261641054465207883005952000000000000))
theorem leaf00528_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 696974200676675950417367007232000000000000 542519511225286362650769676397360512499712 4786269261641054465207883005952000000000000 raw00528=true := by decide +kernel
#print axioms leaf00528_raw
theorem leaf00528_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00528=true := by decide +kernel
#print axioms leaf00528_rectangular
def affine00528 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00528 (IntegerComputedClassCell.leftNumerator ![(3/200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/200),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00528_transform : affine00528=(NestedInteger.clearedAll 3 raw00528 (IntegerComputedClassCell.leftNumerator ![(3/200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/200),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/200),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00528_transform
theorem leaf00528_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00528=true := by decide +kernel
#print axioms leaf00528_sign
theorem leaf00528_log : RationalLog.accepts (3002805081/4294967296) (-192144531/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00528_log
def leaf00528 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (113349141381/1000000000000) (3002805081/4294967296) (-192144531/1073741824) 1 8 ![60,0,4] ![(3/200),0,(1/4)] ![(1/3200),1,(1/4)] affine00528
theorem leaf00528_checked : FastNestedCellData.accepts 1 2 4 leaf00528=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (113349141381/1000000000000) (3002805081/4294967296) (-192144531/1073741824) 1 8 ![60,0,4] ![(3/200),0,(1/4)] ![(1/3200),1,(1/4)] 696974200676675950417367007232000000000000 542519511225286362650769676397360512499712 4786269261641054465207883005952000000000000 raw00528 affine00528
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00528_raw leaf00528_rectangular
    leaf00528_transform leaf00528_sign leaf00528_log
#print axioms leaf00528_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
