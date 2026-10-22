/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00611 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 9449809444019519649517009895424000000000000 3145000720171100308713636636009619230031872 6139279711438452146709356085248000000000000))
theorem leaf00611_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 9449809444019519649517009895424000000000000 3145000720171100308713636636009619230031872 6139279711438452146709356085248000000000000 raw00611=true := by decide +kernel
#print axioms leaf00611_raw
theorem leaf00611_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00611=true := by decide +kernel
#print axioms leaf00611_rectangular
def affine00611 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00611 (IntegerComputedClassCell.leftNumerator ![(131/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(131/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(131/6400),0,(1/16)] ![(3/6400),1,(1/16)]))
theorem leaf00611_transform : affine00611=(NestedInteger.clearedAll 3 raw00611 (IntegerComputedClassCell.leftNumerator ![(131/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(131/6400),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(131/6400),0,(1/16)] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00611_transform
theorem leaf00611_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00611=true := by decide +kernel
#print axioms leaf00611_sign
theorem leaf00611_log : RationalLog.accepts (945206567/4294967296) (-812712919/1073741824) 3 8=true := by decide +kernel
#print axioms leaf00611_log
def leaf00611 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (512275196439/1000000000000) (945206567/4294967296) (-812712919/1073741824) 3 8 ![60,0,4] ![(131/6400),0,(1/16)] ![(3/6400),1,(1/16)] affine00611
theorem leaf00611_checked : FastNestedCellData.accepts 1 2 4 leaf00611=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (512275196439/1000000000000) (945206567/4294967296) (-812712919/1073741824) 3 8 ![60,0,4] ![(131/6400),0,(1/16)] ![(3/6400),1,(1/16)] 9449809444019519649517009895424000000000000 3145000720171100308713636636009619230031872 6139279711438452146709356085248000000000000 raw00611 affine00611
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00611_raw leaf00611_rectangular
    leaf00611_transform leaf00611_sign leaf00611_log
#print axioms leaf00611_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
