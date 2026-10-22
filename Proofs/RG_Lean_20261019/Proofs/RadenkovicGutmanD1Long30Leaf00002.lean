/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00002 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 74018122193047841891216785408000000000000 71205289069489804261806795569498731577344 4436432947912442761885643702272000000000000))
theorem leaf00002_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 74018122193047841891216785408000000000000 71205289069489804261806795569498731577344 4436432947912442761885643702272000000000000 raw00002=true := by decide +kernel
#print axioms leaf00002_raw
theorem leaf00002_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00002=true := by decide +kernel
#print axioms leaf00002_rectangular
def affine00002 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00002 (IntegerComputedClassCell.leftNumerator ![(1/1000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/1000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/1000),0,(1/8)] ![(1/16000),1,(1/8)]))
theorem leaf00002_transform : affine00002=(NestedInteger.clearedAll 3 raw00002 (IntegerComputedClassCell.leftNumerator ![(1/1000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/1000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/1000),0,(1/8)] ![(1/16000),1,(1/8)])) := by decide +kernel
#print axioms leaf00002_transform
theorem leaf00002_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00002=true := by decide +kernel
#print axioms leaf00002_sign
theorem leaf00002_log : RationalLog.accepts (2033241307/2147483648) (-117393385/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00002_log
def leaf00002 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (16050121777/1000000000000) (2033241307/2147483648) (-117393385/4294967296) 1 8 ![60,0,4] ![(1/1000),0,(1/8)] ![(1/16000),1,(1/8)] affine00002
theorem leaf00002_checked : FastNestedCellData.accepts 1 2 4 leaf00002=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (16050121777/1000000000000) (2033241307/2147483648) (-117393385/4294967296) 1 8 ![60,0,4] ![(1/1000),0,(1/8)] ![(1/16000),1,(1/8)] 74018122193047841891216785408000000000000 71205289069489804261806795569498731577344 4436432947912442761885643702272000000000000 raw00002 affine00002
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00002_raw leaf00002_rectangular
    leaf00002_transform leaf00002_sign leaf00002_log
#print axioms leaf00002_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
