/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00906 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 210318353004682513274915258368000000000000 61259405299283594311040571535022251573248 83952832360994971662138998784000000000000))
theorem leaf00906_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 210318353004682513274915258368000000000000 61259405299283594311040571535022251573248 83952832360994971662138998784000000000000 raw00906=true := by decide +kernel
#print axioms leaf00906_raw
theorem leaf00906_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00906=true := by decide +kernel
#print axioms leaf00906_rectangular
def affine00906 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00906 (IntegerComputedClassCell.leftNumerator ![(9/128),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/128),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/128),0,(1/16)] ![(1/640),1,(1/16)]))
theorem leaf00906_transform : affine00906=(NestedInteger.clearedAll 3 raw00906 (IntegerComputedClassCell.leftNumerator ![(9/128),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(9/128),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(9/128),0,(1/16)] ![(1/640),1,(1/16)])) := by decide +kernel
#print axioms leaf00906_transform
theorem leaf00906_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00906=true := by decide +kernel
#print axioms leaf00906_sign
theorem leaf00906_log : RationalLog.accepts (361624299/2147483648) (-1912813361/2147483648) 3 8=true := by decide +kernel
#print axioms leaf00906_log
def leaf00906 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (182422092193/250000000000) (361624299/2147483648) (-1912813361/2147483648) 3 8 ![60,0,4] ![(9/128),0,(1/16)] ![(1/640),1,(1/16)] affine00906
theorem leaf00906_checked : FastNestedCellData.accepts 1 2 4 leaf00906=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (182422092193/250000000000) (361624299/2147483648) (-1912813361/2147483648) 3 8 ![60,0,4] ![(9/128),0,(1/16)] ![(1/640),1,(1/16)] 210318353004682513274915258368000000000000 61259405299283594311040571535022251573248 83952832360994971662138998784000000000000 raw00906 affine00906
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00906_raw leaf00906_rectangular
    leaf00906_transform leaf00906_sign leaf00906_log
#print axioms leaf00906_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
