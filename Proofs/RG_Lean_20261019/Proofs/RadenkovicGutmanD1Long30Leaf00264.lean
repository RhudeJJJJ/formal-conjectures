/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00264 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 24252731233898682365996171264000000000000 23078499890018206465064226537040313843712 1097101128968042179088464478208000000000000))
theorem leaf00264_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 24252731233898682365996171264000000000000 23078499890018206465064226537040313843712 1097101128968042179088464478208000000000000 raw00264=true := by decide +kernel
#print axioms leaf00264_raw
theorem leaf00264_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00264=true := by decide +kernel
#print axioms leaf00264_rectangular
def affine00264 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00264 (IntegerComputedClassCell.leftNumerator ![(9/1600),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/1600),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/1600),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00264_transform : affine00264=(NestedInteger.clearedAll 3 raw00264 (IntegerComputedClassCell.leftNumerator ![(9/1600),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/1600),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/1600),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00264_transform
theorem leaf00264_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00264=true := by decide +kernel
#print axioms leaf00264_sign
theorem leaf00264_log : RationalLog.accepts (2001408681/2147483648) (-18910071/536870912) 1 8=true := by decide +kernel
#print axioms leaf00264_log
def leaf00264 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (10517945557/500000000000) (2001408681/2147483648) (-18910071/536870912) 1 8 ![60,0,4] ![(9/1600),0,(1/2)] ![(1/6400),1,(1/2)] affine00264
theorem leaf00264_checked : FastNestedCellData.accepts 1 2 4 leaf00264=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (10517945557/500000000000) (2001408681/2147483648) (-18910071/536870912) 1 8 ![60,0,4] ![(9/1600),0,(1/2)] ![(1/6400),1,(1/2)] 24252731233898682365996171264000000000000 23078499890018206465064226537040313843712 1097101128968042179088464478208000000000000 raw00264 affine00264
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00264_raw leaf00264_rectangular
    leaf00264_transform leaf00264_sign leaf00264_log
#print axioms leaf00264_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
