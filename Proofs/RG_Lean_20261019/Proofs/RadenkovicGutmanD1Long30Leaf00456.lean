/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00456 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 6262471936183819143958990159872000000000000 2991984417760896872122513563634348144459776 8813192520363593718948406755328000000000000))
theorem leaf00456_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 6262471936183819143958990159872000000000000 2991984417760896872122513563634348144459776 8813192520363593718948406755328000000000000 raw00456=true := by decide +kernel
#print axioms leaf00456_raw
theorem leaf00456_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00456=true := by decide +kernel
#print axioms leaf00456_rectangular
def affine00456 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00456 (IntegerComputedClassCell.leftNumerator ![(3/256),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/256),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/256),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00456_transform : affine00456=(NestedInteger.clearedAll 3 raw00456 (IntegerComputedClassCell.leftNumerator ![(3/256),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/256),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/256),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00456_transform
theorem leaf00456_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00456=true := by decide +kernel
#print axioms leaf00456_sign
theorem leaf00456_log : RationalLog.accepts (1531913179/4294967296) (-553474491/1073741824) 2 8=true := by decide +kernel
#print axioms leaf00456_log
def leaf00456 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (339489283917/1000000000000) (1531913179/4294967296) (-553474491/1073741824) 2 8 ![60,0,4] ![(3/256),0,(1/16)] ![(1/6400),1,(1/16)] affine00456
theorem leaf00456_checked : FastNestedCellData.accepts 1 2 4 leaf00456=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (339489283917/1000000000000) (1531913179/4294967296) (-553474491/1073741824) 2 8 ![60,0,4] ![(3/256),0,(1/16)] ![(1/6400),1,(1/16)] 6262471936183819143958990159872000000000000 2991984417760896872122513563634348144459776 8813192520363593718948406755328000000000000 raw00456 affine00456
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00456_raw leaf00456_rectangular
    leaf00456_transform leaf00456_sign leaf00456_log
#print axioms leaf00456_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
