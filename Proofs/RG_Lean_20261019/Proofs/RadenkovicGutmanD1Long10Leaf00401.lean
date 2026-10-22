/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00401 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 194541644616857647228005646336000000000000 260300976842152734913960210933170892177408 1542634197744833803434304995328000000000000))
theorem leaf00401_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 194541644616857647228005646336000000000000 260300976842152734913960210933170892177408 1542634197744833803434304995328000000000000 raw00401=true := by decide +kernel
#print axioms leaf00401_raw
theorem leaf00401_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00401=true := by decide +kernel
#print axioms leaf00401_rectangular
def affine00401 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00401 (IntegerComputedClassCell.leftNumerator ![(3/4),0,(3/4)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,(3/4)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/4),0,(3/4)] ![(1/8),1,(1/4)]))
theorem leaf00401_transform : affine00401=(NestedInteger.clearedAll 3 raw00401 (IntegerComputedClassCell.leftNumerator ![(3/4),0,(3/4)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,(3/4)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/4),0,(3/4)] ![(1/8),1,(1/4)])) := by decide +kernel
#print axioms leaf00401_transform
theorem leaf00401_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00401=true := by decide +kernel
#print axioms leaf00401_sign
theorem leaf00401_log : RationalLog.accepts (2458532329/2147483648) (145242691/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00401_log
def leaf00401 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (84368989493/500000000000) (2458532329/2147483648) (145242691/2147483648) 0 8 ![52,0,4] ![(3/4),0,(3/4)] ![(1/8),1,(1/4)] affine00401
theorem leaf00401_checked : FastNestedCellData.accepts 1 0 4 leaf00401=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (84368989493/500000000000) (2458532329/2147483648) (145242691/2147483648) 0 8 ![52,0,4] ![(3/4),0,(3/4)] ![(1/8),1,(1/4)] 194541644616857647228005646336000000000000 260300976842152734913960210933170892177408 1542634197744833803434304995328000000000000 raw00401 affine00401
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00401_raw leaf00401_rectangular
    leaf00401_transform leaf00401_sign leaf00401_log
#print axioms leaf00401_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
