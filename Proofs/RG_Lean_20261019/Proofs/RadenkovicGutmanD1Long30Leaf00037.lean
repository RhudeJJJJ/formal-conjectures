/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00037 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 6587075321365382511275802624000000000000 6240253847973679761096116875841406763008 273054523613796551935601410048000000000000))
theorem leaf00037_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 6587075321365382511275802624000000000000 6240253847973679761096116875841406763008 273054523613796551935601410048000000000000 raw00037=true := by decide +kernel
#print axioms leaf00037_raw
theorem leaf00037_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00037=true := by decide +kernel
#print axioms leaf00037_rectangular
def affine00037 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00037 (IntegerComputedClassCell.leftNumerator ![(23/16000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(23/16000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(23/16000),0,(1/8)] ![(1/16000),1,(1/8)]))
theorem leaf00037_transform : affine00037=(NestedInteger.clearedAll 3 raw00037 (IntegerComputedClassCell.leftNumerator ![(23/16000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(23/16000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(23/16000),0,(1/8)] ![(1/16000),1,(1/8)])) := by decide +kernel
#print axioms leaf00037_transform
theorem leaf00037_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00037=true := by decide +kernel
#print axioms leaf00037_sign
theorem leaf00037_log : RationalLog.accepts (1988960021/2147483648) (-164679521/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00037_log
def leaf00037 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (5713377099/250000000000) (1988960021/2147483648) (-164679521/4294967296) 1 8 ![60,0,4] ![(23/16000),0,(1/8)] ![(1/16000),1,(1/8)] affine00037
theorem leaf00037_checked : FastNestedCellData.accepts 1 2 4 leaf00037=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (5713377099/250000000000) (1988960021/2147483648) (-164679521/4294967296) 1 8 ![60,0,4] ![(23/16000),0,(1/8)] ![(1/16000),1,(1/8)] 6587075321365382511275802624000000000000 6240253847973679761096116875841406763008 273054523613796551935601410048000000000000 raw00037 affine00037
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00037_raw leaf00037_rectangular
    leaf00037_transform leaf00037_sign leaf00037_log
#print axioms leaf00037_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
