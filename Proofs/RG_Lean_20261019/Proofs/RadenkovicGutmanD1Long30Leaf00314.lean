/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00314 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 123509622677674852091516944384000000000000 116027602597213123876897262443852271190016 4332317280618951053646543978496000000000000))
theorem leaf00314_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 123509622677674852091516944384000000000000 116027602597213123876897262443852271190016 4332317280618951053646543978496000000000000 raw00314=true := by decide +kernel
#print axioms leaf00314_raw
theorem leaf00314_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00314=true := by decide +kernel
#print axioms leaf00314_rectangular
def affine00314 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00314 (IntegerComputedClassCell.leftNumerator ![(23/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(23/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(23/3200),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00314_transform : affine00314=(NestedInteger.clearedAll 3 raw00314 (IntegerComputedClassCell.leftNumerator ![(23/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(23/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(23/3200),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00314_transform
theorem leaf00314_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00314=true := by decide +kernel
#print axioms leaf00314_sign
theorem leaf00314_log : RationalLog.accepts (3929544299/4294967296) (-190955305/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00314_log
def leaf00314 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (13390940123/500000000000) (3929544299/4294967296) (-190955305/4294967296) 1 8 ![60,0,4] ![(23/3200),0,(1/2)] ![(1/6400),1,(1/2)] affine00314
theorem leaf00314_checked : FastNestedCellData.accepts 1 2 4 leaf00314=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (13390940123/500000000000) (3929544299/4294967296) (-190955305/4294967296) 1 8 ![60,0,4] ![(23/3200),0,(1/2)] ![(1/6400),1,(1/2)] 123509622677674852091516944384000000000000 116027602597213123876897262443852271190016 4332317280618951053646543978496000000000000 raw00314 affine00314
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00314_raw leaf00314_rectangular
    leaf00314_transform leaf00314_sign leaf00314_log
#print axioms leaf00314_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
