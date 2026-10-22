/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00167 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 651439117213577598428669542400000000000 571975668269388883256979440455523500032 10122865370447947564325850316800000000000))
theorem leaf00167_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 651439117213577598428669542400000000000 571975668269388883256979440455523500032 10122865370447947564325850316800000000000 raw00167=true := by decide +kernel
#print axioms leaf00167_raw
theorem leaf00167_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00167=true := by decide +kernel
#print axioms leaf00167_rectangular
def affine00167 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00167 (IntegerComputedClassCell.leftNumerator ![(23/6400),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(23/6400),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(23/6400),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00167_transform : affine00167=(NestedInteger.clearedAll 3 raw00167 (IntegerComputedClassCell.leftNumerator ![(23/6400),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(23/6400),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(23/6400),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00167_transform
theorem leaf00167_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00167=true := by decide +kernel
#print axioms leaf00167_sign
theorem leaf00167_log : RationalLog.accepts (892344843/1073741824) (-397396621/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00167_log
def leaf00167 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (5650333649/100000000000) (892344843/1073741824) (-397396621/4294967296) 1 8 ![60,0,4] ![(23/6400),0,(1/8)] ![(3/32000),1,(1/8)] affine00167
theorem leaf00167_checked : FastNestedCellData.accepts 1 2 4 leaf00167=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (5650333649/100000000000) (892344843/1073741824) (-397396621/4294967296) 1 8 ![60,0,4] ![(23/6400),0,(1/8)] ![(3/32000),1,(1/8)] 651439117213577598428669542400000000000 571975668269388883256979440455523500032 10122865370447947564325850316800000000000 raw00167 affine00167
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00167_raw leaf00167_rectangular
    leaf00167_transform leaf00167_sign leaf00167_log
#print axioms leaf00167_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
