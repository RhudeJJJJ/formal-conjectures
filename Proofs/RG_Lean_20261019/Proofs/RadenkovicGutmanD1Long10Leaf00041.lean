/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00041 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 297505512132067334318366654464000000000000 285589444989621512491407271227613620731904 17707891743322276917445159550976000000000000))
theorem leaf00041_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 297505512132067334318366654464000000000000 285589444989621512491407271227613620731904 17707891743322276917445159550976000000000000 raw00041=true := by decide +kernel
#print axioms leaf00041_raw
theorem leaf00041_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00041=true := by decide +kernel
#print axioms leaf00041_rectangular
def affine00041 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00041 (IntegerComputedClassCell.leftNumerator ![(17/4000),0,(1/2)] ![(3/8000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/4000),0,(1/2)] ![(3/8000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/4000),0,(1/2)] ![(3/8000),1,(1/2)]))
theorem leaf00041_transform : affine00041=(NestedInteger.clearedAll 3 raw00041 (IntegerComputedClassCell.leftNumerator ![(17/4000),0,(1/2)] ![(3/8000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/4000),0,(1/2)] ![(3/8000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/4000),0,(1/2)] ![(3/8000),1,(1/2)])) := by decide +kernel
#print axioms leaf00041_transform
theorem leaf00041_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00041=true := by decide +kernel
#print axioms leaf00041_sign
theorem leaf00041_log : RationalLog.accepts (4057501239/4294967296) (-122141637/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00041_log
def leaf00041 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (16127806129/1000000000000) (4057501239/4294967296) (-122141637/4294967296) 1 8 ![52,0,4] ![(17/4000),0,(1/2)] ![(3/8000),1,(1/2)] affine00041
theorem leaf00041_checked : FastNestedCellData.accepts 1 0 4 leaf00041=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (16127806129/1000000000000) (4057501239/4294967296) (-122141637/4294967296) 1 8 ![52,0,4] ![(17/4000),0,(1/2)] ![(3/8000),1,(1/2)] 297505512132067334318366654464000000000000 285589444989621512491407271227613620731904 17707891743322276917445159550976000000000000 raw00041 affine00041
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00041_raw leaf00041_rectangular
    leaf00041_transform leaf00041_sign leaf00041_log
#print axioms leaf00041_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
