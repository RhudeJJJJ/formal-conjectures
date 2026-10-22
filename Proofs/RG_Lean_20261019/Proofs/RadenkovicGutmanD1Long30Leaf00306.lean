/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00306 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 570443671738970716634238418944000000000000 352508895894762368234667278903574962110464 1628467130919744933928137392128000000000000))
theorem leaf00306_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 570443671738970716634238418944000000000000 352508895894762368234667278903574962110464 1628467130919744933928137392128000000000000 raw00306=true := by decide +kernel
#print axioms leaf00306_raw
theorem leaf00306_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00306=true := by decide +kernel
#print axioms leaf00306_rectangular
def affine00306 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00306 (IntegerComputedClassCell.leftNumerator ![(9/1280),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/1280),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/1280),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00306_transform : affine00306=(NestedInteger.clearedAll 3 raw00306 (IntegerComputedClassCell.leftNumerator ![(9/1280),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/1280),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/1280),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00306_transform
theorem leaf00306_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00306=true := by decide +kernel
#print axioms leaf00306_sign
theorem leaf00306_log : RationalLog.accepts (2181810127/4294967296) (-727233625/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00306_log
def leaf00306 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (216466693863/1000000000000) (2181810127/4294967296) (-727233625/2147483648) 1 8 ![60,0,4] ![(9/1280),0,(1/16)] ![(1/6400),1,(1/16)] affine00306
theorem leaf00306_checked : FastNestedCellData.accepts 1 2 4 leaf00306=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (216466693863/1000000000000) (2181810127/4294967296) (-727233625/2147483648) 1 8 ![60,0,4] ![(9/1280),0,(1/16)] ![(1/6400),1,(1/16)] 570443671738970716634238418944000000000000 352508895894762368234667278903574962110464 1628467130919744933928137392128000000000000 raw00306 affine00306
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00306_raw leaf00306_rectangular
    leaf00306_transform leaf00306_sign leaf00306_log
#print axioms leaf00306_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
