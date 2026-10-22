/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00966 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 265768349462380792866712584192000000000000 107490459289480229211801641967513998721024 155433685395070533569949466624000000000000))
theorem leaf00966_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 265768349462380792866712584192000000000000 107490459289480229211801641967513998721024 155433685395070533569949466624000000000000 raw00966=true := by decide +kernel
#print axioms leaf00966_raw
theorem leaf00966_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00966=true := by decide +kernel
#print axioms leaf00966_rectangular
def affine00966 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00966 (IntegerComputedClassCell.leftNumerator ![(17/160),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/160),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/160),0,(1/16)] ![(1/160),1,(1/16)]))
theorem leaf00966_transform : affine00966=(NestedInteger.clearedAll 3 raw00966 (IntegerComputedClassCell.leftNumerator ![(17/160),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/160),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/160),0,(1/16)] ![(1/160),1,(1/16)])) := by decide +kernel
#print axioms leaf00966_transform
theorem leaf00966_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00966=true := by decide +kernel
#print axioms leaf00966_sign
theorem leaf00966_log : RationalLog.accepts (1026930837/4294967296) (-1536384327/2147483648) 3 8=true := by decide +kernel
#print axioms leaf00966_log
def leaf00966 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (172887973119/250000000000) (1026930837/4294967296) (-1536384327/2147483648) 3 8 ![60,0,4] ![(17/160),0,(1/16)] ![(1/160),1,(1/16)] affine00966
theorem leaf00966_checked : FastNestedCellData.accepts 1 2 4 leaf00966=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (172887973119/250000000000) (1026930837/4294967296) (-1536384327/2147483648) 3 8 ![60,0,4] ![(17/160),0,(1/16)] ![(1/160),1,(1/16)] 265768349462380792866712584192000000000000 107490459289480229211801641967513998721024 155433685395070533569949466624000000000000 raw00966 affine00966
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00966_raw leaf00966_rectangular
    leaf00966_transform leaf00966_sign leaf00966_log
#print axioms leaf00966_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
