/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00032 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 100912562012471695819377999872000000000000 95808720578925218381362313214259271565312 4378441378612894540454097321984000000000000))
theorem leaf00032_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 100912562012471695819377999872000000000000 95808720578925218381362313214259271565312 4378441378612894540454097321984000000000000 raw00032=true := by decide +kernel
#print axioms leaf00032_raw
theorem leaf00032_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00032=true := by decide +kernel
#print axioms leaf00032_rectangular
def affine00032 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00032 (IntegerComputedClassCell.leftNumerator ![(11/8000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(11/8000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(11/8000),0,(1/8)] ![(1/16000),1,(1/8)]))
theorem leaf00032_transform : affine00032=(NestedInteger.clearedAll 3 raw00032 (IntegerComputedClassCell.leftNumerator ![(11/8000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(11/8000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(11/8000),0,(1/8)] ![(1/16000),1,(1/8)])) := by decide +kernel
#print axioms leaf00032_transform
theorem leaf00032_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00032=true := by decide +kernel
#print axioms leaf00032_sign
theorem leaf00032_log : RationalLog.accepts (1995211581/2147483648) (-78970143/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00032_log
def leaf00032 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (21881923793/1000000000000) (1995211581/2147483648) (-78970143/2147483648) 1 8 ![60,0,4] ![(11/8000),0,(1/8)] ![(1/16000),1,(1/8)] affine00032
theorem leaf00032_checked : FastNestedCellData.accepts 1 2 4 leaf00032=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (21881923793/1000000000000) (1995211581/2147483648) (-78970143/2147483648) 1 8 ![60,0,4] ![(11/8000),0,(1/8)] ![(1/16000),1,(1/8)] 100912562012471695819377999872000000000000 95808720578925218381362313214259271565312 4378441378612894540454097321984000000000000 raw00032 affine00032
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00032_raw leaf00032_rectangular
    leaf00032_transform leaf00032_sign leaf00032_log
#print axioms leaf00032_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
