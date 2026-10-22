/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00461 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 75372024133342677054833819648000000000000 35732313565998936728171732879934002036736 104109747787823170547842285568000000000000))
theorem leaf00461_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 75372024133342677054833819648000000000000 35732313565998936728171732879934002036736 104109747787823170547842285568000000000000 raw00461=true := by decide +kernel
#print axioms leaf00461_raw
theorem leaf00461_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00461=true := by decide +kernel
#print axioms leaf00461_rectangular
def affine00461 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00461 (IntegerComputedClassCell.leftNumerator ![(19/1600),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/1600),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/1600),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00461_transform : affine00461=(NestedInteger.clearedAll 3 raw00461 (IntegerComputedClassCell.leftNumerator ![(19/1600),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/1600),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/1600),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00461_transform
theorem leaf00461_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00461=true := by decide +kernel
#print axioms leaf00461_sign
theorem leaf00461_log : RationalLog.accepts (1515878511/4294967296) (-279561791/536870912) 2 8=true := by decide +kernel
#print axioms leaf00461_log
def leaf00461 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (171608875851/500000000000) (1515878511/4294967296) (-279561791/536870912) 2 8 ![60,0,4] ![(19/1600),0,(1/16)] ![(1/6400),1,(1/16)] affine00461
theorem leaf00461_checked : FastNestedCellData.accepts 1 2 4 leaf00461=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (171608875851/500000000000) (1515878511/4294967296) (-279561791/536870912) 2 8 ![60,0,4] ![(19/1600),0,(1/16)] ![(1/6400),1,(1/16)] 75372024133342677054833819648000000000000 35732313565998936728171732879934002036736 104109747787823170547842285568000000000000 raw00461 affine00461
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00461_raw leaf00461_rectangular
    leaf00461_transform leaf00461_sign leaf00461_log
#print axioms leaf00461_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
