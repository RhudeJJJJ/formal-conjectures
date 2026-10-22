/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00256 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 32041154453854366048932855808000000000000 17312011535711944090991896728316409806848 51910817841758264671221055488000000000000))
theorem leaf00256_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 32041154453854366048932855808000000000000 17312011535711944090991896728316409806848 51910817841758264671221055488000000000000 raw00256=true := by decide +kernel
#print axioms leaf00256_raw
theorem leaf00256_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00256=true := by decide +kernel
#print axioms leaf00256_rectangular
def affine00256 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00256 (IntegerComputedClassCell.leftNumerator ![(33/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(33/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(33/640),0,(1/4)] ![(1/640),1,(1/4)]))
theorem leaf00256_transform : affine00256=(NestedInteger.clearedAll 3 raw00256 (IntegerComputedClassCell.leftNumerator ![(33/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(33/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(33/640),0,(1/4)] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00256_transform
theorem leaf00256_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00256=true := by decide +kernel
#print axioms leaf00256_sign
theorem leaf00256_log : RationalLog.accepts (217529307/536870912) (-242511067/536870912) 2 8=true := by decide +kernel
#print axioms leaf00256_log
def leaf00256 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (333495256971/1000000000000) (217529307/536870912) (-242511067/536870912) 2 8 ![52,0,4] ![(33/640),0,(1/4)] ![(1/640),1,(1/4)] affine00256
theorem leaf00256_checked : FastNestedCellData.accepts 1 0 4 leaf00256=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (333495256971/1000000000000) (217529307/536870912) (-242511067/536870912) 2 8 ![52,0,4] ![(33/640),0,(1/4)] ![(1/640),1,(1/4)] 32041154453854366048932855808000000000000 17312011535711944090991896728316409806848 51910817841758264671221055488000000000000 raw00256 affine00256
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00256_raw leaf00256_rectangular
    leaf00256_transform leaf00256_sign leaf00256_log
#print axioms leaf00256_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
