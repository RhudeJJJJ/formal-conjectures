/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00951 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 203711368370692793076514029568000000000000 75863378634250600400886076547292632973312 107338781997183729118841143296000000000000))
theorem leaf00951_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 203711368370692793076514029568000000000000 75863378634250600400886076547292632973312 107338781997183729118841143296000000000000 raw00951=true := by decide +kernel
#print axioms leaf00951_raw
theorem leaf00951_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00951=true := by decide +kernel
#print axioms leaf00951_rectangular
def affine00951 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00951 (IntegerComputedClassCell.leftNumerator ![(31/320),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/320),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/320),0,(1/16)] ![(1/320),1,(1/16)]))
theorem leaf00951_transform : affine00951=(NestedInteger.clearedAll 3 raw00951 (IntegerComputedClassCell.leftNumerator ![(31/320),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(31/320),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(31/320),0,(1/16)] ![(1/320),1,(1/16)])) := by decide +kernel
#print axioms leaf00951_transform
theorem leaf00951_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00951=true := by decide +kernel
#print axioms leaf00951_sign
theorem leaf00951_log : RationalLog.accepts (937136487/4294967296) (-1634632699/2147483648) 3 8=true := by decide +kernel
#print axioms leaf00951_log
def leaf00951 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (88345723259/125000000000) (937136487/4294967296) (-1634632699/2147483648) 3 8 ![60,0,4] ![(31/320),0,(1/16)] ![(1/320),1,(1/16)] affine00951
theorem leaf00951_checked : FastNestedCellData.accepts 1 2 4 leaf00951=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (88345723259/125000000000) (937136487/4294967296) (-1634632699/2147483648) 3 8 ![60,0,4] ![(31/320),0,(1/16)] ![(1/320),1,(1/16)] 203711368370692793076514029568000000000000 75863378634250600400886076547292632973312 107338781997183729118841143296000000000000 raw00951 affine00951
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00951_raw leaf00951_rectangular
    leaf00951_transform leaf00951_sign leaf00951_log
#print axioms leaf00951_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
