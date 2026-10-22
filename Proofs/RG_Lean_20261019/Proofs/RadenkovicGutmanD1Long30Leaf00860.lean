/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00860 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1000067781073364846552702517248000000000000 111904059785298936004498402515652385439744 129007852688553682496995196928000000000000))
theorem leaf00860_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1000067781073364846552702517248000000000000 111904059785298936004498402515652385439744 129007852688553682496995196928000000000000 raw00860=true := by decide +kernel
#print axioms leaf00860_raw
theorem leaf00860_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00860=true := by decide +kernel
#print axioms leaf00860_rectangular
def affine00860 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00860 (IntegerComputedClassCell.leftNumerator ![(9/160),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/160),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/160),0,0] ![(1/640),1,(1/16)]))
theorem leaf00860_transform : affine00860=(NestedInteger.clearedAll 3 raw00860 (IntegerComputedClassCell.leftNumerator ![(9/160),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/160),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/160),0,0] ![(1/640),1,(1/16)])) := by decide +kernel
#print axioms leaf00860_transform
theorem leaf00860_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00860=true := by decide +kernel
#print axioms leaf00860_sign
theorem leaf00860_log : RationalLog.accepts (128677953/2147483648) (-6044606679/4294967296) 5 8=true := by decide +kernel
#print axioms leaf00860_log
def leaf00860 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (433710264349/500000000000) (128677953/2147483648) (-6044606679/4294967296) 5 8 ![60,0,4] ![(9/160),0,0] ![(1/640),1,(1/16)] affine00860
theorem leaf00860_checked : FastNestedCellData.accepts 1 2 4 leaf00860=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (433710264349/500000000000) (128677953/2147483648) (-6044606679/4294967296) 5 8 ![60,0,4] ![(9/160),0,0] ![(1/640),1,(1/16)] 1000067781073364846552702517248000000000000 111904059785298936004498402515652385439744 129007852688553682496995196928000000000000 raw00860 affine00860
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00860_raw leaf00860_rectangular
    leaf00860_transform leaf00860_sign leaf00860_log
#print axioms leaf00860_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
