/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00490 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 19964603050349816764484812800000000000 20003287561852037902116868010249551872 924124374914222454606703624192000000000000))
theorem leaf00490_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 19964603050349816764484812800000000000 20003287561852037902116868010249551872 924124374914222454606703624192000000000000 raw00490=true := by decide +kernel
#print axioms leaf00490_raw
theorem leaf00490_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00490=true := by decide +kernel
#print axioms leaf00490_rectangular
def affine00490 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00490 (IntegerComputedClassCell.leftNumerator ![(1/32),0,0] ![(1/128),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/32),0,0] ![(1/128),1,1]) (IntegerComputedClassCell.denominator ![(1/32),0,0] ![(1/128),1,1]))
theorem leaf00490_transform : affine00490=(NestedInteger.clearedAll 3 raw00490 (IntegerComputedClassCell.leftNumerator ![(1/32),0,0] ![(1/128),1,1]) (IntegerComputedClassCell.widthNumerator ![(1/32),0,0] ![(1/128),1,1]) (IntegerComputedClassCell.denominator ![(1/32),0,0] ![(1/128),1,1])) := by decide +kernel
#print axioms leaf00490_transform
theorem leaf00490_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00490=true := by decide +kernel
#print axioms leaf00490_sign
theorem leaf00490_log : RationalLog.accepts (4303196315/4294967296) (1027643/1073741824) 0 8=true := by decide +kernel
#print axioms leaf00490_log
def leaf00490 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (10822833/500000000000) (4303196315/4294967296) (1027643/1073741824) 0 8 ![52,0,4] ![(1/32),0,0] ![(1/128),1,1] affine00490
theorem leaf00490_checked : FastNestedCellData.accepts 1 0 4 leaf00490=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (10822833/500000000000) (4303196315/4294967296) (1027643/1073741824) 0 8 ![52,0,4] ![(1/32),0,0] ![(1/128),1,1] 19964603050349816764484812800000000000 20003287561852037902116868010249551872 924124374914222454606703624192000000000000 raw00490 affine00490
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00490_raw leaf00490_rectangular
    leaf00490_transform leaf00490_sign leaf00490_log
#print axioms leaf00490_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
