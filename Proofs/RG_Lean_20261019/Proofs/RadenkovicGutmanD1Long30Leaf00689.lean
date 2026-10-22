/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00689 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 18440247425041293969062384107520000000000 14882482884258522757713625204013509115904 148877261036352372132053778432000000000000))
theorem leaf00689_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 18440247425041293969062384107520000000000 14882482884258522757713625204013509115904 148877261036352372132053778432000000000000 raw00689=true := by decide +kernel
#print axioms leaf00689_raw
theorem leaf00689_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00689=true := by decide +kernel
#print axioms leaf00689_rectangular
def affine00689 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00689 (IntegerComputedClassCell.leftNumerator ![(11/400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/400),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00689_transform : affine00689=(NestedInteger.clearedAll 3 raw00689 (IntegerComputedClassCell.leftNumerator ![(11/400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/400),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00689_transform
theorem leaf00689_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00689=true := by decide +kernel
#print axioms leaf00689_sign
theorem leaf00689_log : RationalLog.accepts (1575649925/2147483648) (-166230771/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00689_log
def leaf00689 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (99964781597/1000000000000) (1575649925/2147483648) (-166230771/1073741824) 1 8 ![60,0,4] ![(11/400),0,(1/2)] ![(3/6400),1,(1/2)] affine00689
theorem leaf00689_checked : FastNestedCellData.accepts 1 2 4 leaf00689=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (99964781597/1000000000000) (1575649925/2147483648) (-166230771/1073741824) 1 8 ![60,0,4] ![(11/400),0,(1/2)] ![(3/6400),1,(1/2)] 18440247425041293969062384107520000000000 14882482884258522757713625204013509115904 148877261036352372132053778432000000000000 raw00689 affine00689
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00689_raw leaf00689_rectangular
    leaf00689_transform leaf00689_sign leaf00689_log
#print axioms leaf00689_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
