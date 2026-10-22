/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00206 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 25195218204901004243455128371200000000000 18521832882847285179525957981038159331328 135608077765899356745845073510400000000000))
theorem leaf00206_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 25195218204901004243455128371200000000000 18521832882847285179525957981038159331328 135608077765899356745845073510400000000000 raw00206=true := by decide +kernel
#print axioms leaf00206_raw
theorem leaf00206_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00206=true := by decide +kernel
#print axioms leaf00206_rectangular
def affine00206 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00206 (IntegerComputedClassCell.leftNumerator ![(139/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(139/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(139/32000),0,(1/16)] ![(3/32000),1,(1/16)]))
theorem leaf00206_transform : affine00206=(NestedInteger.clearedAll 3 raw00206 (IntegerComputedClassCell.leftNumerator ![(139/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(139/32000),0,(1/16)] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(139/32000),0,(1/16)] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00206_transform
theorem leaf00206_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00206=true := by decide +kernel
#print axioms leaf00206_sign
theorem leaf00206_log : RationalLog.accepts (2777949407/4294967296) (-935725037/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00206_log
def leaf00206 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (13658355157/100000000000) (2777949407/4294967296) (-935725037/4294967296) 1 8 ![60,0,4] ![(139/32000),0,(1/16)] ![(3/32000),1,(1/16)] affine00206
theorem leaf00206_checked : FastNestedCellData.accepts 1 2 4 leaf00206=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (13658355157/100000000000) (2777949407/4294967296) (-935725037/4294967296) 1 8 ![60,0,4] ![(139/32000),0,(1/16)] ![(3/32000),1,(1/16)] 25195218204901004243455128371200000000000 18521832882847285179525957981038159331328 135608077765899356745845073510400000000000 raw00206 affine00206
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00206_raw leaf00206_rectangular
    leaf00206_transform leaf00206_sign leaf00206_log
#print axioms leaf00206_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
