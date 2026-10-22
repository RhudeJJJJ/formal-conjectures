/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00678 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3559738226655878076448590790656000000000000 2381748740394722136613905483331231901810688 12342342797272435692009599008768000000000000))
theorem leaf00678_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3559738226655878076448590790656000000000000 2381748740394722136613905483331231901810688 12342342797272435692009599008768000000000000 raw00678=true := by decide +kernel
#print axioms leaf00678_raw
theorem leaf00678_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00678=true := by decide +kernel
#print axioms leaf00678_rectangular
def affine00678 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00678 (IntegerComputedClassCell.leftNumerator ![(17/640),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/640),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/640),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00678_transform : affine00678=(NestedInteger.clearedAll 3 raw00678 (IntegerComputedClassCell.leftNumerator ![(17/640),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/640),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/640),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00678_transform
theorem leaf00678_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00678=true := by decide +kernel
#print axioms leaf00678_sign
theorem leaf00678_log : RationalLog.accepts (2408833813/4294967296) (-620946209/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00678_log
def leaf00678 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (192973795941/1000000000000) (2408833813/4294967296) (-620946209/2147483648) 1 8 ![60,0,4] ![(17/640),0,(1/4)] ![(3/6400),1,(1/4)] affine00678
theorem leaf00678_checked : FastNestedCellData.accepts 1 2 4 leaf00678=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (192973795941/1000000000000) (2408833813/4294967296) (-620946209/2147483648) 1 8 ![60,0,4] ![(17/640),0,(1/4)] ![(3/6400),1,(1/4)] 3559738226655878076448590790656000000000000 2381748740394722136613905483331231901810688 12342342797272435692009599008768000000000000 raw00678 affine00678
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00678_raw leaf00678_rectangular
    leaf00678_transform leaf00678_sign leaf00678_log
#print axioms leaf00678_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
