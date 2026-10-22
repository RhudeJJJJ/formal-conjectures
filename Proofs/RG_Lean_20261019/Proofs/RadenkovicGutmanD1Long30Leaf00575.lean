/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00575 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 23613509523144117464502108160000000000 281165916699765389659664574163451904 343195736542188295013007360000000000))
theorem leaf00575_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 23613509523144117464502108160000000000 281165916699765389659664574163451904 343195736542188295013007360000000000 raw00575=true := by decide +kernel
#print axioms leaf00575_raw
theorem leaf00575_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00575=true := by decide +kernel
#print axioms leaf00575_rectangular
def affine00575 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00575 (IntegerComputedClassCell.leftNumerator ![(29/1600),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(29/1600),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(29/1600),0,0] ![(1/3200),1,(1/16)]))
theorem leaf00575_transform : affine00575=(NestedInteger.clearedAll 3 raw00575 (IntegerComputedClassCell.leftNumerator ![(29/1600),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(29/1600),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(29/1600),0,0] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00575_transform
theorem leaf00575_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00575=true := by decide +kernel
#print axioms leaf00575_sign
theorem leaf00575_log : RationalLog.accepts (28110441/4294967296) (-5399910209/2147483648) 8 8=true := by decide +kernel
#print axioms leaf00575_log
def leaf00575 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (1024072733/1250000000) (28110441/4294967296) (-5399910209/2147483648) 8 8 ![60,0,4] ![(29/1600),0,0] ![(1/3200),1,(1/16)] affine00575
theorem leaf00575_checked : FastNestedCellData.accepts 1 2 4 leaf00575=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (1024072733/1250000000) (28110441/4294967296) (-5399910209/2147483648) 8 8 ![60,0,4] ![(29/1600),0,0] ![(1/3200),1,(1/16)] 23613509523144117464502108160000000000 281165916699765389659664574163451904 343195736542188295013007360000000000 raw00575 affine00575
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00575_raw leaf00575_rectangular
    leaf00575_transform leaf00575_sign leaf00575_log
#print axioms leaf00575_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
