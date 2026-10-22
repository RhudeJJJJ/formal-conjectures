/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00304 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 29553520614651226414492155904000000000000 27834357564059143248895497732643339894784 1085854704789754773345136541696000000000000))
theorem leaf00304_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 29553520614651226414492155904000000000000 27834357564059143248895497732643339894784 1085854704789754773345136541696000000000000 raw00304=true := by decide +kernel
#print axioms leaf00304_raw
theorem leaf00304_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00304=true := by decide +kernel
#print axioms leaf00304_rectangular
def affine00304 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00304 (IntegerComputedClassCell.leftNumerator ![(11/1600),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/1600),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/1600),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00304_transform : affine00304=(NestedInteger.clearedAll 3 raw00304 (IntegerComputedClassCell.leftNumerator ![(11/1600),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/1600),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/1600),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00304_transform
theorem leaf00304_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00304=true := by decide +kernel
#print axioms leaf00304_sign
theorem leaf00304_log : RationalLog.accepts (3944024479/4294967296) (-45764119/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00304_log
def leaf00304 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (6408398251/250000000000) (3944024479/4294967296) (-45764119/1073741824) 1 8 ![60,0,4] ![(11/1600),0,(1/2)] ![(1/6400),1,(1/2)] affine00304
theorem leaf00304_checked : FastNestedCellData.accepts 1 2 4 leaf00304=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (6408398251/250000000000) (3944024479/4294967296) (-45764119/1073741824) 1 8 ![60,0,4] ![(11/1600),0,(1/2)] ![(1/6400),1,(1/2)] 29553520614651226414492155904000000000000 27834357564059143248895497732643339894784 1085854704789754773345136541696000000000000 raw00304 affine00304
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00304_raw leaf00304_rectangular
    leaf00304_transform leaf00304_sign leaf00304_log
#print axioms leaf00304_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
