/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00354 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 27503876315465217585313113702400000000000 16359320305270061080786866900009465413632 27430333040135001307461399347200000000000))
theorem leaf00354_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 27503876315465217585313113702400000000000 16359320305270061080786866900009465413632 27430333040135001307461399347200000000000 raw00354=true := by decide +kernel
#print axioms leaf00354_raw
theorem leaf00354_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00354=true := by decide +kernel
#print axioms leaf00354_rectangular
def affine00354 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00354 (IntegerComputedClassCell.leftNumerator ![(3/16),0,0] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,0] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/16),0,0] ![(1/80),1,(1/4)]))
theorem leaf00354_transform : affine00354=(NestedInteger.clearedAll 3 raw00354 (IntegerComputedClassCell.leftNumerator ![(3/16),0,0] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/16),0,0] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/16),0,0] ![(1/80),1,(1/4)])) := by decide +kernel
#print axioms leaf00354_transform
theorem leaf00354_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00354=true := by decide +kernel
#print axioms leaf00354_sign
theorem leaf00354_log : RationalLog.accepts (1600260863/4294967296) (-1060080949/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00354_log
def leaf00354 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (29819762453/50000000000) (1600260863/4294967296) (-1060080949/2147483648) 2 8 ![52,0,4] ![(3/16),0,0] ![(1/80),1,(1/4)] affine00354
theorem leaf00354_checked : FastNestedCellData.accepts 1 0 4 leaf00354=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (29819762453/50000000000) (1600260863/4294967296) (-1060080949/2147483648) 2 8 ![52,0,4] ![(3/16),0,0] ![(1/80),1,(1/4)] 27503876315465217585313113702400000000000 16359320305270061080786866900009465413632 27430333040135001307461399347200000000000 raw00354 affine00354
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00354_raw leaf00354_rectangular
    leaf00354_transform leaf00354_sign leaf00354_log
#print axioms leaf00354_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
