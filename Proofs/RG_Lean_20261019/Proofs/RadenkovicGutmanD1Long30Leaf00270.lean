/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00270 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3610114751409364711100246917120000000000 3385087306587145551061506325655584768 6918765026779073661066280960000000000))
theorem leaf00270_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3610114751409364711100246917120000000000 3385087306587145551061506325655584768 6918765026779073661066280960000000000 raw00270=true := by decide +kernel
#print axioms leaf00270_raw
theorem leaf00270_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00270=true := by decide +kernel
#print axioms leaf00270_rectangular
def affine00270 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00270 (IntegerComputedClassCell.leftNumerator ![(19/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/3200),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00270_transform : affine00270=(NestedInteger.clearedAll 3 raw00270 (IntegerComputedClassCell.leftNumerator ![(19/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/3200),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00270_transform
theorem leaf00270_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00270=true := by decide +kernel
#print axioms leaf00270_sign
theorem leaf00270_log : RationalLog.accepts (2704193/4294967296) (-15827804609/4294967296) 11 8=true := by decide +kernel
#print axioms leaf00270_log
def leaf00270 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (9785235641/20000000000) (2704193/4294967296) (-15827804609/4294967296) 11 8 ![60,0,4] ![(19/3200),0,0] ![(1/6400),1,(1/16)] affine00270
theorem leaf00270_checked : FastNestedCellData.accepts 1 2 4 leaf00270=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (9785235641/20000000000) (2704193/4294967296) (-15827804609/4294967296) 11 8 ![60,0,4] ![(19/3200),0,0] ![(1/6400),1,(1/16)] 3610114751409364711100246917120000000000 3385087306587145551061506325655584768 6918765026779073661066280960000000000 raw00270 affine00270
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00270_raw leaf00270_rectangular
    leaf00270_transform leaf00270_sign leaf00270_log
#print axioms leaf00270_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
