/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00008 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2401683788048131554396864512000000000000 2353441163537907796937761144069114822656 282440692314761550258002460672000000000000))
theorem leaf00008_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2401683788048131554396864512000000000000 2353441163537907796937761144069114822656 282440692314761550258002460672000000000000 raw00008=true := by decide +kernel
#print axioms leaf00008_raw
theorem leaf00008_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00008=true := by decide +kernel
#print axioms leaf00008_rectangular
def affine00008 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00008 (IntegerComputedClassCell.leftNumerator ![(17/16000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/16000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/16000),0,(1/4)] ![(1/16000),1,(1/4)]))
theorem leaf00008_transform : affine00008=(NestedInteger.clearedAll 3 raw00008 (IntegerComputedClassCell.leftNumerator ![(17/16000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/16000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/16000),0,(1/4)] ![(1/16000),1,(1/4)])) := by decide +kernel
#print axioms leaf00008_transform
theorem leaf00008_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00008=true := by decide +kernel
#print axioms leaf00008_sign
theorem leaf00008_log : RationalLog.accepts (1043478769/1073741824) (-30697737/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00008_log
def leaf00008 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (4166257249/500000000000) (1043478769/1073741824) (-30697737/2147483648) 1 8 ![60,0,4] ![(17/16000),0,(1/4)] ![(1/16000),1,(1/4)] affine00008
theorem leaf00008_checked : FastNestedCellData.accepts 1 2 4 leaf00008=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (4166257249/500000000000) (1043478769/1073741824) (-30697737/2147483648) 1 8 ![60,0,4] ![(17/16000),0,(1/4)] ![(1/16000),1,(1/4)] 2401683788048131554396864512000000000000 2353441163537907796937761144069114822656 282440692314761550258002460672000000000000 raw00008 affine00008
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00008_raw leaf00008_rectangular
    leaf00008_transform leaf00008_sign leaf00008_log
#print axioms leaf00008_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
