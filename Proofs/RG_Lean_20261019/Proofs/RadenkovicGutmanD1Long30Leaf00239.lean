/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00239 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 5267172479956777292177342464000000000000 5046137034146237766002683070146813100032 276134867616294292473272860672000000000000))
theorem leaf00239_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 5267172479956777292177342464000000000000 5046137034146237766002683070146813100032 276134867616294292473272860672000000000000 raw00239=true := by decide +kernel
#print axioms leaf00239_raw
theorem leaf00239_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00239=true := by decide +kernel
#print axioms leaf00239_rectangular
def affine00239 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00239 (IntegerComputedClassCell.leftNumerator ![(157/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(157/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(157/32000),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00239_transform : affine00239=(NestedInteger.clearedAll 3 raw00239 (IntegerComputedClassCell.leftNumerator ![(157/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(157/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(157/32000),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00239_transform
theorem leaf00239_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00239=true := by decide +kernel
#print axioms leaf00239_sign
theorem leaf00239_log : RationalLog.accepts (1010221577/1073741824) (-130953353/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00239_log
def leaf00239 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (9137087753/500000000000) (1010221577/1073741824) (-130953353/4294967296) 1 8 ![60,0,4] ![(157/32000),0,(1/2)] ![(3/32000),1,(1/2)] affine00239
theorem leaf00239_checked : FastNestedCellData.accepts 1 2 4 leaf00239=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (9137087753/500000000000) (1010221577/1073741824) (-130953353/4294967296) 1 8 ![60,0,4] ![(157/32000),0,(1/2)] ![(3/32000),1,(1/2)] 5267172479956777292177342464000000000000 5046137034146237766002683070146813100032 276134867616294292473272860672000000000000 raw00239 affine00239
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00239_raw leaf00239_rectangular
    leaf00239_transform leaf00239_sign leaf00239_log
#print axioms leaf00239_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
