/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00633 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 6094422712004243015486427627520000000000 4285223666057125768440301423852768985088 25941234470217092777126972620800000000000))
theorem leaf00633_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 6094422712004243015486427627520000000000 4285223666057125768440301423852768985088 25941234470217092777126972620800000000000 raw00633=true := by decide +kernel
#print axioms leaf00633_raw
theorem leaf00633_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00633=true := by decide +kernel
#print axioms leaf00633_rectangular
def affine00633 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00633 (IntegerComputedClassCell.leftNumerator ![(143/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(143/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(143/6400),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00633_transform : affine00633=(NestedInteger.clearedAll 3 raw00633 (IntegerComputedClassCell.leftNumerator ![(143/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(143/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(143/6400),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00633_transform
theorem leaf00633_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00633=true := by decide +kernel
#print axioms leaf00633_sign
theorem leaf00633_log : RationalLog.accepts (2591815965/4294967296) (-1084662171/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00633_log
def leaf00633 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (16518965861/100000000000) (2591815965/4294967296) (-1084662171/4294967296) 1 8 ![60,0,4] ![(143/6400),0,(1/4)] ![(3/6400),1,(1/4)] affine00633
theorem leaf00633_checked : FastNestedCellData.accepts 1 2 4 leaf00633=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (16518965861/100000000000) (2591815965/4294967296) (-1084662171/4294967296) 1 8 ![60,0,4] ![(143/6400),0,(1/4)] ![(3/6400),1,(1/4)] 6094422712004243015486427627520000000000 4285223666057125768440301423852768985088 25941234470217092777126972620800000000000 raw00633 affine00633
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00633_raw leaf00633_rectangular
    leaf00633_transform leaf00633_sign leaf00633_log
#print axioms leaf00633_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
