/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00259 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 25162231975111395374108613017600000000000 23975002381039166692009166163786401316864 1171758089735595248807906902016000000000000))
theorem leaf00259_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 25162231975111395374108613017600000000000 23975002381039166692009166163786401316864 1171758089735595248807906902016000000000000 raw00259=true := by decide +kernel
#print axioms leaf00259_raw
theorem leaf00259_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00259=true := by decide +kernel
#print axioms leaf00259_rectangular
def affine00259 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00259 (IntegerComputedClassCell.leftNumerator ![(7/1280),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/1280),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/1280),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00259_transform : affine00259=(NestedInteger.clearedAll 3 raw00259 (IntegerComputedClassCell.leftNumerator ![(7/1280),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/1280),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/1280),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00259_transform
theorem leaf00259_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00259=true := by decide +kernel
#print axioms leaf00259_sign
theorem leaf00259_log : RationalLog.accepts (4010264985/4294967296) (-147288683/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00259_log
def leaf00259 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (20460709929/1000000000000) (4010264985/4294967296) (-147288683/4294967296) 1 8 ![60,0,4] ![(7/1280),0,(1/2)] ![(1/6400),1,(1/2)] affine00259
theorem leaf00259_checked : FastNestedCellData.accepts 1 2 4 leaf00259=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (20460709929/1000000000000) (4010264985/4294967296) (-147288683/4294967296) 1 8 ![60,0,4] ![(7/1280),0,(1/2)] ![(1/6400),1,(1/2)] 25162231975111395374108613017600000000000 23975002381039166692009166163786401316864 1171758089735595248807906902016000000000000 raw00259 affine00259
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00259_raw leaf00259_rectangular
    leaf00259_transform leaf00259_sign leaf00259_log
#print axioms leaf00259_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
