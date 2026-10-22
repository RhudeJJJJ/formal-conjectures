/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00162 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 145088429235833447751870316544000000000000 127797048105452470407069442132534049636352 2321184842919819479630116552704000000000000))
theorem leaf00162_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 145088429235833447751870316544000000000000 127797048105452470407069442132534049636352 2321184842919819479630116552704000000000000 raw00162=true := by decide +kernel
#print axioms leaf00162_raw
theorem leaf00162_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00162=true := by decide +kernel
#print axioms leaf00162_rectangular
def affine00162 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00162 (IntegerComputedClassCell.leftNumerator ![(7/2000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/2000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/2000),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00162_transform : affine00162=(NestedInteger.clearedAll 3 raw00162 (IntegerComputedClassCell.leftNumerator ![(7/2000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/2000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/2000),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00162_transform
theorem leaf00162_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00162=true := by decide +kernel
#print axioms leaf00162_sign
theorem leaf00162_log : RationalLog.accepts (3585684361/4294967296) (-387609215/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00162_log
def leaf00162 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (55056816563/1000000000000) (3585684361/4294967296) (-387609215/4294967296) 1 8 ![60,0,4] ![(7/2000),0,(1/8)] ![(3/32000),1,(1/8)] affine00162
theorem leaf00162_checked : FastNestedCellData.accepts 1 2 4 leaf00162=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (55056816563/1000000000000) (3585684361/4294967296) (-387609215/4294967296) 1 8 ![60,0,4] ![(7/2000),0,(1/8)] ![(3/32000),1,(1/8)] 145088429235833447751870316544000000000000 127797048105452470407069442132534049636352 2321184842919819479630116552704000000000000 raw00162 affine00162
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00162_raw leaf00162_rectangular
    leaf00162_transform leaf00162_sign leaf00162_log
#print axioms leaf00162_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
