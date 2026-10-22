/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00707 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 111783179536328922506217914368000000000000 51191085347098529881436984210377851011072 131995044750121379935369035776000000000000))
theorem leaf00707_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 111783179536328922506217914368000000000000 51191085347098529881436984210377851011072 131995044750121379935369035776000000000000 raw00707=true := by decide +kernel
#print axioms leaf00707_raw
theorem leaf00707_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00707=true := by decide +kernel
#print axioms leaf00707_rectangular
def affine00707 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00707 (IntegerComputedClassCell.leftNumerator ![(47/1600),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(47/1600),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(47/1600),0,(1/8)] ![(3/6400),1,(1/8)]))
theorem leaf00707_transform : affine00707=(NestedInteger.clearedAll 3 raw00707 (IntegerComputedClassCell.leftNumerator ![(47/1600),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(47/1600),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(47/1600),0,(1/8)] ![(3/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00707_transform
theorem leaf00707_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00707=true := by decide +kernel
#print axioms leaf00707_sign
theorem leaf00707_log : RationalLog.accepts (354309493/1073741824) (-2380988321/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00707_log
def leaf00707 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (193912905761/500000000000) (354309493/1073741824) (-2380988321/4294967296) 2 8 ![60,0,4] ![(47/1600),0,(1/8)] ![(3/6400),1,(1/8)] affine00707
theorem leaf00707_checked : FastNestedCellData.accepts 1 2 4 leaf00707=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (193912905761/500000000000) (354309493/1073741824) (-2380988321/4294967296) 2 8 ![60,0,4] ![(47/1600),0,(1/8)] ![(3/6400),1,(1/8)] 111783179536328922506217914368000000000000 51191085347098529881436984210377851011072 131995044750121379935369035776000000000000 raw00707 affine00707
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00707_raw leaf00707_rectangular
    leaf00707_transform leaf00707_sign leaf00707_log
#print axioms leaf00707_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
