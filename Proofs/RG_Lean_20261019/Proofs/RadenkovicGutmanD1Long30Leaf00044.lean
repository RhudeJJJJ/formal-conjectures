/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00044 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 417149040536576504089070796800000000 411472452094986127200945726164041728 72782878823497012474219069440000000000))
theorem leaf00044_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 417149040536576504089070796800000000 411472452094986127200945726164041728 72782878823497012474219069440000000000 raw00044=true := by decide +kernel
#print axioms leaf00044_raw
theorem leaf00044_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00044=true := by decide +kernel
#print axioms leaf00044_rectangular
def affine00044 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00044 (IntegerComputedClassCell.leftNumerator ![(3/2000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/2000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/2000),0,(1/2)] ![(1/16000),1,(1/2)]))
theorem leaf00044_transform : affine00044=(NestedInteger.clearedAll 3 raw00044 (IntegerComputedClassCell.leftNumerator ![(3/2000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(3/2000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(3/2000),0,(1/2)] ![(1/16000),1,(1/2)])) := by decide +kernel
#print axioms leaf00044_transform
theorem leaf00044_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00044=true := by decide +kernel
#print axioms leaf00044_sign
theorem leaf00044_log : RationalLog.accepts (4212704925/4294967296) (-41530223/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00044_log
def leaf00044 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (56534237/10000000000) (4212704925/4294967296) (-41530223/4294967296) 1 8 ![60,0,4] ![(3/2000),0,(1/2)] ![(1/16000),1,(1/2)] affine00044
theorem leaf00044_checked : FastNestedCellData.accepts 1 2 4 leaf00044=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (56534237/10000000000) (4212704925/4294967296) (-41530223/4294967296) 1 8 ![60,0,4] ![(3/2000),0,(1/2)] ![(1/16000),1,(1/2)] 417149040536576504089070796800000000 411472452094986127200945726164041728 72782878823497012474219069440000000000 raw00044 affine00044
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00044_raw leaf00044_rectangular
    leaf00044_transform leaf00044_sign leaf00044_log
#print axioms leaf00044_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
