/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00132 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 53454507515548123789883604992000000000000 47997404649925382878741607316547581247488 1035221210673765879341817790464000000000000))
theorem leaf00132_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 53454507515548123789883604992000000000000 47997404649925382878741607316547581247488 1035221210673765879341817790464000000000000 raw00132=true := by decide +kernel
#print axioms leaf00132_raw
theorem leaf00132_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00132=true := by decide +kernel
#print axioms leaf00132_rectangular
def affine00132 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00132 (IntegerComputedClassCell.leftNumerator ![(47/16000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(47/16000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(47/16000),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00132_transform : affine00132=(NestedInteger.clearedAll 3 raw00132 (IntegerComputedClassCell.leftNumerator ![(47/16000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(47/16000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(47/16000),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00132_transform
theorem leaf00132_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00132=true := by decide +kernel
#print axioms leaf00132_sign
theorem leaf00132_log : RationalLog.accepts (1842809041/2147483648) (-328577275/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00132_log
def leaf00132 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (23182197271/500000000000) (1842809041/2147483648) (-328577275/4294967296) 1 8 ![60,0,4] ![(47/16000),0,(1/8)] ![(3/32000),1,(1/8)] affine00132
theorem leaf00132_checked : FastNestedCellData.accepts 1 2 4 leaf00132=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (23182197271/500000000000) (1842809041/2147483648) (-328577275/4294967296) 1 8 ![60,0,4] ![(47/16000),0,(1/8)] ![(3/32000),1,(1/8)] 53454507515548123789883604992000000000000 47997404649925382878741607316547581247488 1035221210673765879341817790464000000000000 raw00132 affine00132
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00132_raw leaf00132_rectangular
    leaf00132_transform leaf00132_sign leaf00132_log
#print axioms leaf00132_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
