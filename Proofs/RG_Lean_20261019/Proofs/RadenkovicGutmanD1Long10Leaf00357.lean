/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00357 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 16973948337523781329889064386560000000000 10860527925784899713407305439531398856704 18884598931829310429905069015040000000000))
theorem leaf00357_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 16973948337523781329889064386560000000000 10860527925784899713407305439531398856704 18884598931829310429905069015040000000000 raw00357=true := by decide +kernel
#print axioms leaf00357_raw
theorem leaf00357_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00357=true := by decide +kernel
#print axioms leaf00357_rectangular
def affine00357 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00357 (IntegerComputedClassCell.leftNumerator ![(1/5),0,0] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/5),0,0] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/5),0,0] ![(3/160),1,(1/4)]))
theorem leaf00357_transform : affine00357=(NestedInteger.clearedAll 3 raw00357 (IntegerComputedClassCell.leftNumerator ![(1/5),0,0] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/5),0,0] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/5),0,0] ![(3/160),1,(1/4)])) := by decide +kernel
#print axioms leaf00357_transform
theorem leaf00357_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00357=true := by decide +kernel
#print axioms leaf00357_sign
theorem leaf00357_log : RationalLog.accepts (1744696389/4294967296) (-1934589469/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00357_log
def leaf00357 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (23003989579/40000000000) (1744696389/4294967296) (-1934589469/4294967296) 2 8 ![52,0,4] ![(1/5),0,0] ![(3/160),1,(1/4)] affine00357
theorem leaf00357_checked : FastNestedCellData.accepts 1 0 4 leaf00357=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (23003989579/40000000000) (1744696389/4294967296) (-1934589469/4294967296) 2 8 ![52,0,4] ![(1/5),0,0] ![(3/160),1,(1/4)] 16973948337523781329889064386560000000000 10860527925784899713407305439531398856704 18884598931829310429905069015040000000000 raw00357 affine00357
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00357_raw leaf00357_rectangular
    leaf00357_transform leaf00357_sign leaf00357_log
#print axioms leaf00357_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
