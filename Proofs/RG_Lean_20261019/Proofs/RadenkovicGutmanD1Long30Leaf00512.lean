/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00512 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 15252071893101964259944824832000000000000 9628162876550553671062989450330618462208 45487738108768311372345769984000000000000))
theorem leaf00512_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 15252071893101964259944824832000000000000 9628162876550553671062989450330618462208 45487738108768311372345769984000000000000 raw00512=true := by decide +kernel
#print axioms leaf00512_raw
theorem leaf00512_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00512=true := by decide +kernel
#print axioms leaf00512_rectangular
def affine00512 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00512 (IntegerComputedClassCell.leftNumerator ![(9/640),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(9/640),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(9/640),0,(1/8)] ![(1/3200),1,(1/8)]))
theorem leaf00512_transform : affine00512=(NestedInteger.clearedAll 3 raw00512 (IntegerComputedClassCell.leftNumerator ![(9/640),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(9/640),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(9/640),0,(1/8)] ![(1/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00512_transform
theorem leaf00512_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00512=true := by decide +kernel
#print axioms leaf00512_sign
theorem leaf00512_log : RationalLog.accepts (279706069/536870912) (-1400198845/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00512_log
def leaf00512 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (105832508681/500000000000) (279706069/536870912) (-1400198845/4294967296) 1 8 ![60,0,4] ![(9/640),0,(1/8)] ![(1/3200),1,(1/8)] affine00512
theorem leaf00512_checked : FastNestedCellData.accepts 1 2 4 leaf00512=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (105832508681/500000000000) (279706069/536870912) (-1400198845/4294967296) 1 8 ![60,0,4] ![(9/640),0,(1/8)] ![(1/3200),1,(1/8)] 15252071893101964259944824832000000000000 9628162876550553671062989450330618462208 45487738108768311372345769984000000000000 raw00512 affine00512
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00512_raw leaf00512_rectangular
    leaf00512_transform leaf00512_sign leaf00512_log
#print axioms leaf00512_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
