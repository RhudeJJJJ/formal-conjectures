/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00262 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 97665539821421726349131776000000000000 52064398139246682958965567195935932416 150051136567664035806314496000000000000))
theorem leaf00262_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 97665539821421726349131776000000000000 52064398139246682958965567195935932416 150051136567664035806314496000000000000 raw00262=true := by decide +kernel
#print axioms leaf00262_raw
theorem leaf00262_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00262=true := by decide +kernel
#print axioms leaf00262_rectangular
def affine00262 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00262 (IntegerComputedClassCell.leftNumerator ![(7/128),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/128),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/128),0,(1/4)] ![(1/640),1,(1/4)]))
theorem leaf00262_transform : affine00262=(NestedInteger.clearedAll 3 raw00262 (IntegerComputedClassCell.leftNumerator ![(7/128),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/128),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/128),0,(1/4)] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00262_transform
theorem leaf00262_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00262=true := by decide +kernel
#print axioms leaf00262_sign
theorem leaf00262_log : RationalLog.accepts (6639861/16777216) (-1990568691/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00262_log
def leaf00262 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (346977699271/1000000000000) (6639861/16777216) (-1990568691/4294967296) 2 8 ![52,0,4] ![(7/128),0,(1/4)] ![(1/640),1,(1/4)] affine00262
theorem leaf00262_checked : FastNestedCellData.accepts 1 0 4 leaf00262=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (346977699271/1000000000000) (6639861/16777216) (-1990568691/4294967296) 2 8 ![52,0,4] ![(7/128),0,(1/4)] ![(1/640),1,(1/4)] 97665539821421726349131776000000000000 52064398139246682958965567195935932416 150051136567664035806314496000000000000 raw00262 affine00262
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00262_raw leaf00262_rectangular
    leaf00262_transform leaf00262_sign leaf00262_log
#print axioms leaf00262_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
