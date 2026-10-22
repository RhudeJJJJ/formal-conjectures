/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00232 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 86746017229786940513942765568000000000000 73103309222267842528791162666992724344832 971599388096582954815349325824000000000000))
theorem leaf00232_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 86746017229786940513942765568000000000000 73103309222267842528791162666992724344832 971599388096582954815349325824000000000000 raw00232=true := by decide +kernel
#print axioms leaf00232_raw
theorem leaf00232_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00232=true := by decide +kernel
#print axioms leaf00232_rectangular
def affine00232 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00232 (IntegerComputedClassCell.leftNumerator ![(77/16000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(77/16000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(77/16000),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00232_transform : affine00232=(NestedInteger.clearedAll 3 raw00232 (IntegerComputedClassCell.leftNumerator ![(77/16000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(77/16000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(77/16000),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00232_transform
theorem leaf00232_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00232=true := by decide +kernel
#print axioms leaf00232_sign
theorem leaf00232_log : RationalLog.accepts (3366215153/4294967296) (-523245009/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00232_log
def leaf00232 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (18810044067/250000000000) (3366215153/4294967296) (-523245009/4294967296) 1 8 ![60,0,4] ![(77/16000),0,(1/8)] ![(3/32000),1,(1/8)] affine00232
theorem leaf00232_checked : FastNestedCellData.accepts 1 2 4 leaf00232=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (18810044067/250000000000) (3366215153/4294967296) (-523245009/4294967296) 1 8 ![60,0,4] ![(77/16000),0,(1/8)] ![(3/32000),1,(1/8)] 86746017229786940513942765568000000000000 73103309222267842528791162666992724344832 971599388096582954815349325824000000000000 raw00232 affine00232
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00232_raw leaf00232_rectangular
    leaf00232_transform leaf00232_sign leaf00232_log
#print axioms leaf00232_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
