/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00559 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 14367624917490438671065887539200000000000 12492847149177998033658301809085988732928 200496215829240120781169491968000000000000))
theorem leaf00559_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 14367624917490438671065887539200000000000 12492847149177998033658301809085988732928 200496215829240120781169491968000000000000 raw00559=true := by decide +kernel
#print axioms leaf00559_raw
theorem leaf00559_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00559=true := by decide +kernel
#print axioms leaf00559_rectangular
def affine00559 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00559 (IntegerComputedClassCell.leftNumerator ![(27/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(27/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(27/1600),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00559_transform : affine00559=(NestedInteger.clearedAll 3 raw00559 (IntegerComputedClassCell.leftNumerator ![(27/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(27/1600),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(27/1600),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00559_transform
theorem leaf00559_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00559=true := by decide +kernel
#print axioms leaf00559_sign
theorem leaf00559_log : RationalLog.accepts (3515484465/4294967296) (-430069279/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00559_log
def leaf00559 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (15577410149/250000000000) (3515484465/4294967296) (-430069279/4294967296) 1 8 ![60,0,4] ![(27/1600),0,(1/2)] ![(1/3200),1,(1/2)] affine00559
theorem leaf00559_checked : FastNestedCellData.accepts 1 2 4 leaf00559=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (15577410149/250000000000) (3515484465/4294967296) (-430069279/4294967296) 1 8 ![60,0,4] ![(27/1600),0,(1/2)] ![(1/3200),1,(1/2)] 14367624917490438671065887539200000000000 12492847149177998033658301809085988732928 200496215829240120781169491968000000000000 raw00559 affine00559
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00559_raw leaf00559_rectangular
    leaf00559_transform leaf00559_sign leaf00559_log
#print axioms leaf00559_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
