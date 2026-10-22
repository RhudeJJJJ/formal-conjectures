/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00923 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 5612352179253131151042569830400000000000 2955406908605537879244677532347428503552 7142548249389529886651056128000000000000))
theorem leaf00923_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 5612352179253131151042569830400000000000 2955406908605537879244677532347428503552 7142548249389529886651056128000000000000 raw00923=true := by decide +kernel
#print axioms leaf00923_raw
theorem leaf00923_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00923=true := by decide +kernel
#print axioms leaf00923_rectangular
def affine00923 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00923 (IntegerComputedClassCell.leftNumerator ![(5/64),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/64),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/64),0,(1/4)] ![(1/320),1,(1/4)]))
theorem leaf00923_transform : affine00923=(NestedInteger.clearedAll 3 raw00923 (IntegerComputedClassCell.leftNumerator ![(5/64),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/64),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/64),0,(1/4)] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00923_transform
theorem leaf00923_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00923=true := by decide +kernel
#print axioms leaf00923_sign
theorem leaf00923_log : RationalLog.accepts (799874735/2147483648) (-530212069/1073741824) 2 8=true := by decide +kernel
#print axioms leaf00923_log
def leaf00923 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (206887430467/500000000000) (799874735/2147483648) (-530212069/1073741824) 2 8 ![60,0,4] ![(5/64),0,(1/4)] ![(1/320),1,(1/4)] affine00923
theorem leaf00923_checked : FastNestedCellData.accepts 1 2 4 leaf00923=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (206887430467/500000000000) (799874735/2147483648) (-530212069/1073741824) 2 8 ![60,0,4] ![(5/64),0,(1/4)] ![(1/320),1,(1/4)] 5612352179253131151042569830400000000000 2955406908605537879244677532347428503552 7142548249389529886651056128000000000000 raw00923 affine00923
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00923_raw leaf00923_rectangular
    leaf00923_transform leaf00923_sign leaf00923_log
#print axioms leaf00923_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
