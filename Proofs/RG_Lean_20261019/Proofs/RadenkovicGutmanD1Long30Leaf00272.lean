/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00272 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 142772885535856619752559476736000000000000 115591219743066866769778346288697588056064 1244565007193870922097394450432000000000000))
theorem leaf00272_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 142772885535856619752559476736000000000000 115591219743066866769778346288697588056064 1244565007193870922097394450432000000000000 raw00272=true := by decide +kernel
#print axioms leaf00272_raw
theorem leaf00272_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00272=true := by decide +kernel
#print axioms leaf00272_rectangular
def affine00272 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00272 (IntegerComputedClassCell.leftNumerator ![(19/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(19/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(19/3200),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00272_transform : affine00272=(NestedInteger.clearedAll 3 raw00272 (IntegerComputedClassCell.leftNumerator ![(19/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(19/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(19/3200),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00272_transform
theorem leaf00272_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00272=true := by decide +kernel
#print axioms leaf00272_sign
theorem leaf00272_log : RationalLog.accepts (3181762527/4294967296) (-644263693/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00272_log
def leaf00272 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (46438401801/500000000000) (3181762527/4294967296) (-644263693/4294967296) 1 8 ![60,0,4] ![(19/3200),0,(1/8)] ![(1/6400),1,(1/8)] affine00272
theorem leaf00272_checked : FastNestedCellData.accepts 1 2 4 leaf00272=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (46438401801/500000000000) (3181762527/4294967296) (-644263693/4294967296) 1 8 ![60,0,4] ![(19/3200),0,(1/8)] ![(1/6400),1,(1/8)] 142772885535856619752559476736000000000000 115591219743066866769778346288697588056064 1244565007193870922097394450432000000000000 raw00272 affine00272
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00272_raw leaf00272_rectangular
    leaf00272_transform leaf00272_sign leaf00272_log
#print axioms leaf00272_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
