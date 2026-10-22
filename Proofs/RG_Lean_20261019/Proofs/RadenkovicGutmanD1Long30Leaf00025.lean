/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00025 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 916210815158905240373166080000000000 14421457955096490658957080133632 113421010270781114941440000000000))
theorem leaf00025_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 916210815158905240373166080000000000 14421457955096490658957080133632 113421010270781114941440000000000 raw00025=true := by decide +kernel
#print axioms leaf00025_raw
theorem leaf00025_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00025=true := by decide +kernel
#print axioms leaf00025_rectangular
def affine00025 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00025 (IntegerComputedClassCell.leftNumerator ![(21/16000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(21/16000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(21/16000),0,0] ![(1/16000),1,(1/16)]))
theorem leaf00025_transform : affine00025=(NestedInteger.clearedAll 3 raw00025 (IntegerComputedClassCell.leftNumerator ![(21/16000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(21/16000),0,0] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(21/16000),0,0] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00025_transform
theorem leaf00025_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00025=true := by decide +kernel
#print axioms leaf00025_sign
theorem leaf00025_log : RationalLog.accepts (29989/2147483648) (-24006670201/4294967296) 17 8=true := by decide +kernel
#print axioms leaf00025_log
def leaf00025 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (158937241/1250000000) (29989/2147483648) (-24006670201/4294967296) 17 8 ![60,0,4] ![(21/16000),0,0] ![(1/16000),1,(1/16)] affine00025
theorem leaf00025_checked : FastNestedCellData.accepts 1 2 4 leaf00025=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (158937241/1250000000) (29989/2147483648) (-24006670201/4294967296) 17 8 ![60,0,4] ![(21/16000),0,0] ![(1/16000),1,(1/16)] 916210815158905240373166080000000000 14421457955096490658957080133632 113421010270781114941440000000000 raw00025 affine00025
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00025_raw leaf00025_rectangular
    leaf00025_transform leaf00025_sign leaf00025_log
#print axioms leaf00025_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
