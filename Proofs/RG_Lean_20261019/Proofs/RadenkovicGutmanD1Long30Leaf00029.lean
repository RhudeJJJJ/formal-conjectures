/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00029 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 5719935229684216205160742912000000000000 5651151562578798028558776531217171873792 1139057332061674066390565257216000000000000))
theorem leaf00029_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 5719935229684216205160742912000000000000 5651151562578798028558776531217171873792 1139057332061674066390565257216000000000000 raw00029=true := by decide +kernel
#print axioms leaf00029_raw
theorem leaf00029_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00029=true := by decide +kernel
#print axioms leaf00029_rectangular
def affine00029 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00029 (IntegerComputedClassCell.leftNumerator ![(21/16000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(21/16000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(21/16000),0,(1/2)] ![(1/16000),1,(1/2)]))
theorem leaf00029_transform : affine00029=(NestedInteger.clearedAll 3 raw00029 (IntegerComputedClassCell.leftNumerator ![(21/16000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(21/16000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(21/16000),0,(1/2)] ![(1/16000),1,(1/2)])) := by decide +kernel
#print axioms leaf00029_transform
theorem leaf00029_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00029=true := by decide +kernel
#print axioms leaf00029_sign
theorem leaf00029_log : RationalLog.accepts (2111185489/2147483648) (-36608465/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00029_log
def leaf00029 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (2480626481/500000000000) (2111185489/2147483648) (-36608465/4294967296) 1 8 ![60,0,4] ![(21/16000),0,(1/2)] ![(1/16000),1,(1/2)] affine00029
theorem leaf00029_checked : FastNestedCellData.accepts 1 2 4 leaf00029=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (2480626481/500000000000) (2111185489/2147483648) (-36608465/4294967296) 1 8 ![60,0,4] ![(21/16000),0,(1/2)] ![(1/16000),1,(1/2)] 5719935229684216205160742912000000000000 5651151562578798028558776531217171873792 1139057332061674066390565257216000000000000 raw00029 affine00029
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00029_raw leaf00029_rectangular
    leaf00029_transform leaf00029_sign leaf00029_log
#print axioms leaf00029_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
