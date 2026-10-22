/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00043 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 179308809679219843736063180800000000000 174373458530017665516786423740976070656 14949175152563707099278317977600000000000))
theorem leaf00043_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 179308809679219843736063180800000000000 174373458530017665516786423740976070656 14949175152563707099278317977600000000000 raw00043=true := by decide +kernel
#print axioms leaf00043_raw
theorem leaf00043_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00043=true := by decide +kernel
#print axioms leaf00043_rectangular
def affine00043 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00043 (IntegerComputedClassCell.leftNumerator ![(3/2000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/2000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/2000),0,(1/4)] ![(1/16000),1,(1/4)]))
theorem leaf00043_transform : affine00043=(NestedInteger.clearedAll 3 raw00043 (IntegerComputedClassCell.leftNumerator ![(3/2000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/2000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/2000),0,(1/4)] ![(1/16000),1,(1/4)])) := by decide +kernel
#print axioms leaf00043_transform
theorem leaf00043_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00043=true := by decide +kernel
#print axioms leaf00043_sign
theorem leaf00043_log : RationalLog.accepts (4128593637/4294967296) (-42420461/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00043_log
def leaf00043 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (583221003/50000000000) (4128593637/4294967296) (-42420461/2147483648) 1 8 ![60,0,4] ![(3/2000),0,(1/4)] ![(1/16000),1,(1/4)] affine00043
theorem leaf00043_checked : FastNestedCellData.accepts 1 2 4 leaf00043=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (583221003/50000000000) (4128593637/4294967296) (-42420461/2147483648) 1 8 ![60,0,4] ![(3/2000),0,(1/4)] ![(1/16000),1,(1/4)] 179308809679219843736063180800000000000 174373458530017665516786423740976070656 14949175152563707099278317977600000000000 raw00043 affine00043
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00043_raw leaf00043_rectangular
    leaf00043_transform leaf00043_sign leaf00043_log
#print axioms leaf00043_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
