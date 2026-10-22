/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00045 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2643052093961689175687168000000000000 68268222108670380212306275467264 454394094993820090368000000000000))
theorem leaf00045_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2643052093961689175687168000000000000 68268222108670380212306275467264 454394094993820090368000000000000 raw00045=true := by decide +kernel
#print axioms leaf00045_raw
theorem leaf00045_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00045=true := by decide +kernel
#print axioms leaf00045_rectangular
def affine00045 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00045 (IntegerComputedClassCell.leftNumerator ![(1/640),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/640),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/640),0,0] ![(1/16000),1,(1/16)]))
theorem leaf00045_transform : affine00045=(NestedInteger.clearedAll 3 raw00045 (IntegerComputedClassCell.leftNumerator ![(1/640),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/640),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/640),0,0] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00045_transform
theorem leaf00045_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00045=true := by decide +kernel
#print axioms leaf00045_sign
theorem leaf00045_log : RationalLog.accepts (48223/2147483648) (-22986603755/4294967296) 16 8=true := by decide +kernel
#print axioms leaf00045_log
def leaf00045 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (293437729/1953125000) (48223/2147483648) (-22986603755/4294967296) 16 8 ![60,0,4] ![(1/640),0,0] ![(1/16000),1,(1/16)] affine00045
theorem leaf00045_checked : FastNestedCellData.accepts 1 2 4 leaf00045=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (293437729/1953125000) (48223/2147483648) (-22986603755/4294967296) 16 8 ![60,0,4] ![(1/640),0,0] ![(1/16000),1,(1/16)] 2643052093961689175687168000000000000 68268222108670380212306275467264 454394094993820090368000000000000 raw00045 affine00045
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00045_raw leaf00045_rectangular
    leaf00045_transform leaf00045_sign leaf00045_log
#print axioms leaf00045_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
