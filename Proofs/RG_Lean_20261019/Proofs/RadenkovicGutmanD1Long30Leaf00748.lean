/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00748 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 53811212334598069604527688908800000000000 33671821813794994207039687491892298121216 144285793923487303434778968064000000000000))
theorem leaf00748_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 53811212334598069604527688908800000000000 33671821813794994207039687491892298121216 144285793923487303434778968064000000000000 raw00748=true := by decide +kernel
#print axioms leaf00748_raw
theorem leaf00748_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00748=true := by decide +kernel
#print axioms leaf00748_rectangular
def affine00748 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00748 (IntegerComputedClassCell.leftNumerator ![(53/1600),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(53/1600),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(53/1600),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00748_transform : affine00748=(NestedInteger.clearedAll 3 raw00748 (IntegerComputedClassCell.leftNumerator ![(53/1600),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(53/1600),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(53/1600),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00748_transform
theorem leaf00748_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00748=true := by decide +kernel
#print axioms leaf00748_sign
theorem leaf00748_log : RationalLog.accepts (544754345/1073741824) (-1457217819/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00748_log
def leaf00748 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (233368933269/1000000000000) (544754345/1073741824) (-1457217819/4294967296) 1 8 ![60,0,4] ![(53/1600),0,(1/4)] ![(3/6400),1,(1/4)] affine00748
theorem leaf00748_checked : FastNestedCellData.accepts 1 2 4 leaf00748=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (233368933269/1000000000000) (544754345/1073741824) (-1457217819/4294967296) 1 8 ![60,0,4] ![(53/1600),0,(1/4)] ![(3/6400),1,(1/4)] 53811212334598069604527688908800000000000 33671821813794994207039687491892298121216 144285793923487303434778968064000000000000 raw00748 affine00748
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00748_raw leaf00748_rectangular
    leaf00748_transform leaf00748_sign leaf00748_log
#print axioms leaf00748_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
