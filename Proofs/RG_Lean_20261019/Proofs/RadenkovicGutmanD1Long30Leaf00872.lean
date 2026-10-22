/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00872 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 8579653124495438075742545510400000000000 3280393426863156809774127091651071442944 5877527635087461388873682124800000000000))
theorem leaf00872_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 8579653124495438075742545510400000000000 3280393426863156809774127091651071442944 5877527635087461388873682124800000000000 raw00872=true := by decide +kernel
#print axioms leaf00872_raw
theorem leaf00872_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00872=true := by decide +kernel
#print axioms leaf00872_rectangular
def affine00872 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00872 (IntegerComputedClassCell.leftNumerator ![(19/320),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(19/320),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.denominator ![(19/320),0,(1/8)] ![(1/640),1,(1/8)]))
theorem leaf00872_transform : affine00872=(NestedInteger.clearedAll 3 raw00872 (IntegerComputedClassCell.leftNumerator ![(19/320),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(19/320),0,(1/8)] ![(1/640),1,(1/8)]) (IntegerComputedClassCell.denominator ![(19/320),0,(1/8)] ![(1/640),1,(1/8)])) := by decide +kernel
#print axioms leaf00872_transform
theorem leaf00872_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00872=true := by decide +kernel
#print axioms leaf00872_sign
theorem leaf00872_log : RationalLog.accepts (263483763/1073741824) (-3017028045/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00872_log
def leaf00872 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (111624942681/200000000000) (263483763/1073741824) (-3017028045/4294967296) 3 8 ![60,0,4] ![(19/320),0,(1/8)] ![(1/640),1,(1/8)] affine00872
theorem leaf00872_checked : FastNestedCellData.accepts 1 2 4 leaf00872=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (111624942681/200000000000) (263483763/1073741824) (-3017028045/4294967296) 3 8 ![60,0,4] ![(19/320),0,(1/8)] ![(1/640),1,(1/8)] 8579653124495438075742545510400000000000 3280393426863156809774127091651071442944 5877527635087461388873682124800000000000 raw00872 affine00872
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00872_raw leaf00872_rectangular
    leaf00872_transform leaf00872_sign leaf00872_log
#print axioms leaf00872_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
