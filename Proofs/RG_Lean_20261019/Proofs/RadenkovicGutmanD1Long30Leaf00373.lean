/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00373 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 79746523708110325703195492352000000000000 68182811407901793642941381166617547767808 985741144083605296911801647104000000000000))
theorem leaf00373_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 79746523708110325703195492352000000000000 68182811407901793642941381166617547767808 985741144083605296911801647104000000000000 raw00373=true := by decide +kernel
#print axioms leaf00373_raw
theorem leaf00373_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00373=true := by decide +kernel
#print axioms leaf00373_rectangular
def affine00373 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00373 (IntegerComputedClassCell.leftNumerator ![(29/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(29/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(29/3200),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00373_transform : affine00373=(NestedInteger.clearedAll 3 raw00373 (IntegerComputedClassCell.leftNumerator ![(29/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(29/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(29/3200),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00373_transform
theorem leaf00373_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00373=true := by decide +kernel
#print axioms leaf00373_sign
theorem leaf00373_log : RationalLog.accepts (1717301771/2147483648) (-60006721/536870912) 1 8=true := by decide +kernel
#print axioms leaf00373_log
def leaf00373 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (34584541701/500000000000) (1717301771/2147483648) (-60006721/536870912) 1 8 ![60,0,4] ![(29/3200),0,(1/4)] ![(1/6400),1,(1/4)] affine00373
theorem leaf00373_checked : FastNestedCellData.accepts 1 2 4 leaf00373=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (34584541701/500000000000) (1717301771/2147483648) (-60006721/536870912) 1 8 ![60,0,4] ![(29/3200),0,(1/4)] ![(1/6400),1,(1/4)] 79746523708110325703195492352000000000000 68182811407901793642941381166617547767808 985741144083605296911801647104000000000000 raw00373 affine00373
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00373_raw leaf00373_rectangular
    leaf00373_transform leaf00373_sign leaf00373_log
#print axioms leaf00373_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
