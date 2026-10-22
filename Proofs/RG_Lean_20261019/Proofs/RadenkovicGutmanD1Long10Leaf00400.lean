/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00400 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 195767771702502989269676589056000000000000 262605899615623505214001810787956609253376 1546546636713893188547899293696000000000000))
theorem leaf00400_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 195767771702502989269676589056000000000000 262605899615623505214001810787956609253376 1546546636713893188547899293696000000000000 raw00400=true := by decide +kernel
#print axioms leaf00400_raw
theorem leaf00400_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00400=true := by decide +kernel
#print axioms leaf00400_rectangular
def affine00400 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00400 (IntegerComputedClassCell.leftNumerator ![(3/4),0,(1/2)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,(1/2)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/4),0,(1/2)] ![(1/8),1,(1/4)]))
theorem leaf00400_transform : affine00400=(NestedInteger.clearedAll 3 raw00400 (IntegerComputedClassCell.leftNumerator ![(3/4),0,(1/2)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/4),0,(1/2)] ![(1/8),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/4),0,(1/2)] ![(1/8),1,(1/4)])) := by decide +kernel
#print axioms leaf00400_transform
theorem leaf00400_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00400=true := by decide +kernel
#print axioms leaf00400_sign
theorem leaf00400_log : RationalLog.accepts (2462526893/2147483648) (146985865/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00400_log
def leaf00400 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (84900737353/500000000000) (2462526893/2147483648) (146985865/2147483648) 0 8 ![52,0,4] ![(3/4),0,(1/2)] ![(1/8),1,(1/4)] affine00400
theorem leaf00400_checked : FastNestedCellData.accepts 1 0 4 leaf00400=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (84900737353/500000000000) (2462526893/2147483648) (146985865/2147483648) 0 8 ![52,0,4] ![(3/4),0,(1/2)] ![(1/8),1,(1/4)] 195767771702502989269676589056000000000000 262605899615623505214001810787956609253376 1546546636713893188547899293696000000000000 raw00400 affine00400
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00400_raw leaf00400_rectangular
    leaf00400_transform leaf00400_sign leaf00400_log
#print axioms leaf00400_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
