/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00156 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 71136544333968455014209814528000000000000 55632879892833615489519738827432720859136 515229201146578133472419774464000000000000))
theorem leaf00156_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 71136544333968455014209814528000000000000 55632879892833615489519738827432720859136 515229201146578133472419774464000000000000 raw00156=true := by decide +kernel
#print axioms leaf00156_raw
theorem leaf00156_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00156=true := by decide +kernel
#print axioms leaf00156_rectangular
def affine00156 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00156 (IntegerComputedClassCell.leftNumerator ![(109/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(109/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(109/32000),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00156_transform : affine00156=(NestedInteger.clearedAll 3 raw00156 (IntegerComputedClassCell.leftNumerator ![(109/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(109/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(109/32000),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00156_transform
theorem leaf00156_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00156=true := by decide +kernel
#print axioms leaf00156_sign
theorem leaf00156_log : RationalLog.accepts (3031572173/4294967296) (-748102995/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00156_log
def leaf00156 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (53988477137/500000000000) (3031572173/4294967296) (-748102995/4294967296) 1 8 ![60,0,4] ![(109/32000),0,(1/16)] ![(3/32000),1,(1/16)] affine00156
theorem leaf00156_checked : FastNestedCellData.accepts 1 2 4 leaf00156=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (53988477137/500000000000) (3031572173/4294967296) (-748102995/4294967296) 1 8 ![60,0,4] ![(109/32000),0,(1/16)] ![(3/32000),1,(1/16)] 71136544333968455014209814528000000000000 55632879892833615489519738827432720859136 515229201146578133472419774464000000000000 raw00156 affine00156
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00156_raw leaf00156_rectangular
    leaf00156_transform leaf00156_sign leaf00156_log
#print axioms leaf00156_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
