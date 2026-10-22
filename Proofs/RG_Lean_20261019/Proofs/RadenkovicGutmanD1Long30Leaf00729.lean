/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00729 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 129946543022983703429069668352000000000000 102491520184188641395385484408864670482432 909332983481507122017799766016000000000000))
theorem leaf00729_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 129946543022983703429069668352000000000000 102491520184188641395385484408864670482432 909332983481507122017799766016000000000000 raw00729=true := by decide +kernel
#print axioms leaf00729_raw
theorem leaf00729_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00729=true := by decide +kernel
#print axioms leaf00729_rectangular
def affine00729 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00729 (IntegerComputedClassCell.leftNumerator ![(1/32),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/32),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/32),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00729_transform : affine00729=(NestedInteger.clearedAll 3 raw00729 (IntegerComputedClassCell.leftNumerator ![(1/32),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/32),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/32),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00729_transform
theorem leaf00729_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00729=true := by decide +kernel
#print axioms leaf00729_sign
theorem leaf00729_log : RationalLog.accepts (1522196859/2147483648) (-23094991/134217728) 1 8=true := by decide +kernel
#print axioms leaf00729_log
def leaf00729 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (56355329701/500000000000) (1522196859/2147483648) (-23094991/134217728) 1 8 ![60,0,4] ![(1/32),0,(1/2)] ![(3/6400),1,(1/2)] affine00729
theorem leaf00729_checked : FastNestedCellData.accepts 1 2 4 leaf00729=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (56355329701/500000000000) (1522196859/2147483648) (-23094991/134217728) 1 8 ![60,0,4] ![(1/32),0,(1/2)] ![(3/6400),1,(1/2)] 129946543022983703429069668352000000000000 102491520184188641395385484408864670482432 909332983481507122017799766016000000000000 raw00729 affine00729
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00729_raw leaf00729_rectangular
    leaf00729_transform leaf00729_sign leaf00729_log
#print axioms leaf00729_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
