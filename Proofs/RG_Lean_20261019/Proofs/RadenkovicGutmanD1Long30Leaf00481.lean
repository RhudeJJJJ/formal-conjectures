/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00481 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 264068103405158798111001070796800000000000 121438259904054549982913454591406755545088 339327691958264044655993054822400000000000))
theorem leaf00481_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 264068103405158798111001070796800000000000 121438259904054549982913454591406755545088 339327691958264044655993054822400000000000 raw00481=true := by decide +kernel
#print axioms leaf00481_raw
theorem leaf00481_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00481=true := by decide +kernel
#print axioms leaf00481_rectangular
def affine00481 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00481 (IntegerComputedClassCell.leftNumerator ![(1/80),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/80),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/80),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00481_transform : affine00481=(NestedInteger.clearedAll 3 raw00481 (IntegerComputedClassCell.leftNumerator ![(1/80),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/80),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/80),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00481_transform
theorem leaf00481_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00481=true := by decide +kernel
#print axioms leaf00481_sign
theorem leaf00481_log : RationalLog.accepts (1454582553/4294967296) (-2325134275/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00481_log
def leaf00481 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (71575802849/200000000000) (1454582553/4294967296) (-2325134275/4294967296) 2 8 ![60,0,4] ![(1/80),0,(1/16)] ![(1/6400),1,(1/16)] affine00481
theorem leaf00481_checked : FastNestedCellData.accepts 1 2 4 leaf00481=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (71575802849/200000000000) (1454582553/4294967296) (-2325134275/4294967296) 2 8 ![60,0,4] ![(1/80),0,(1/16)] ![(1/6400),1,(1/16)] 264068103405158798111001070796800000000000 121438259904054549982913454591406755545088 339327691958264044655993054822400000000000 raw00481 affine00481
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00481_raw leaf00481_rectangular
    leaf00481_transform leaf00481_sign leaf00481_log
#print axioms leaf00481_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
