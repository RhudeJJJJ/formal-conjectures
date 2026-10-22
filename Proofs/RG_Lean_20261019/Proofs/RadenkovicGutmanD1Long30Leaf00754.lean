/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00754 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2223535695204698004242953142272000000000000 1730021811210121161441819804642896760537088 14352488094593256167814373310464000000000000))
theorem leaf00754_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2223535695204698004242953142272000000000000 1730021811210121161441819804642896760537088 14352488094593256167814373310464000000000000 raw00754=true := by decide +kernel
#print axioms leaf00754_raw
theorem leaf00754_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00754=true := by decide +kernel
#print axioms leaf00754_rectangular
def affine00754 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00754 (IntegerComputedClassCell.leftNumerator ![(43/1280),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(43/1280),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(43/1280),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00754_transform : affine00754=(NestedInteger.clearedAll 3 raw00754 (IntegerComputedClassCell.leftNumerator ![(43/1280),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(43/1280),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(43/1280),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00754_transform
theorem leaf00754_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00754=true := by decide +kernel
#print axioms leaf00754_sign
theorem leaf00754_log : RationalLog.accepts (2982227027/4294967296) (-391672683/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00754_log
def leaf00754 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (120538111567/1000000000000) (2982227027/4294967296) (-391672683/2147483648) 1 8 ![60,0,4] ![(43/1280),0,(1/2)] ![(3/6400),1,(1/2)] affine00754
theorem leaf00754_checked : FastNestedCellData.accepts 1 2 4 leaf00754=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (120538111567/1000000000000) (2982227027/4294967296) (-391672683/2147483648) 1 8 ![60,0,4] ![(43/1280),0,(1/2)] ![(3/6400),1,(1/2)] 2223535695204698004242953142272000000000000 1730021811210121161441819804642896760537088 14352488094593256167814373310464000000000000 raw00754 affine00754
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00754_raw leaf00754_rectangular
    leaf00754_transform leaf00754_sign leaf00754_log
#print axioms leaf00754_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
