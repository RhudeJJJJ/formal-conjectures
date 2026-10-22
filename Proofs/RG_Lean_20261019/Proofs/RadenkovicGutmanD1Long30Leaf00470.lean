/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00470 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 83131047053506325250048000000000000 420539790325809421996138935877632 576950401317027708928000000000000))
theorem leaf00470_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 83131047053506325250048000000000000 420539790325809421996138935877632 576950401317027708928000000000000 raw00470=true := by decide +kernel
#print axioms leaf00470_raw
theorem leaf00470_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00470=true := by decide +kernel
#print axioms leaf00470_rectangular
def affine00470 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00470 (IntegerComputedClassCell.leftNumerator ![(39/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(39/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(39/3200),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00470_transform : affine00470=(NestedInteger.clearedAll 3 raw00470 (IntegerComputedClassCell.leftNumerator ![(39/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(39/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(39/3200),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00470_transform
theorem leaf00470_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00470=true := by decide +kernel
#print axioms leaf00470_sign
theorem leaf00470_log : RationalLog.accepts (785441/268435456) (-3132169637/1073741824) 9 8=true := by decide +kernel
#print axioms leaf00470_log
def leaf00470 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (22778159817/31250000000) (785441/268435456) (-3132169637/1073741824) 9 8 ![60,0,4] ![(39/3200),0,0] ![(1/6400),1,(1/16)] affine00470
theorem leaf00470_checked : FastNestedCellData.accepts 1 2 4 leaf00470=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (22778159817/31250000000) (785441/268435456) (-3132169637/1073741824) 9 8 ![60,0,4] ![(39/3200),0,0] ![(1/6400),1,(1/16)] 83131047053506325250048000000000000 420539790325809421996138935877632 576950401317027708928000000000000 raw00470 affine00470
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00470_raw leaf00470_rectangular
    leaf00470_transform leaf00470_sign leaf00470_log
#print axioms leaf00470_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
