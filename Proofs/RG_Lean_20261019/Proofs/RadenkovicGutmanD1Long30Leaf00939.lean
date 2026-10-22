/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00939 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 19065104305674465412139450368000000000000 12592341289704530778556672602086861438976 47593435739583111977974628352000000000000))
theorem leaf00939_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 19065104305674465412139450368000000000000 12592341289704530778556672602086861438976 47593435739583111977974628352000000000000 raw00939=true := by decide +kernel
#print axioms leaf00939_raw
theorem leaf00939_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00939=true := by decide +kernel
#print axioms leaf00939_rectangular
def affine00939 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00939 (IntegerComputedClassCell.leftNumerator ![(7/80),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/80),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/80),0,(1/2)] ![(1/320),1,(1/2)]))
theorem leaf00939_transform : affine00939=(NestedInteger.clearedAll 3 raw00939 (IntegerComputedClassCell.leftNumerator ![(7/80),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/80),0,(1/2)] ![(1/320),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/80),0,(1/2)] ![(1/320),1,(1/2)])) := by decide +kernel
#print axioms leaf00939_transform
theorem leaf00939_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00939=true := by decide +kernel
#print axioms leaf00939_sign
theorem leaf00939_log : RationalLog.accepts (1121631897/2147483648) (-1394816617/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00939_log
def leaf00939 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (33072684011/125000000000) (1121631897/2147483648) (-1394816617/4294967296) 1 8 ![60,0,4] ![(7/80),0,(1/2)] ![(1/320),1,(1/2)] affine00939
theorem leaf00939_checked : FastNestedCellData.accepts 1 2 4 leaf00939=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (33072684011/125000000000) (1121631897/2147483648) (-1394816617/4294967296) 1 8 ![60,0,4] ![(7/80),0,(1/2)] ![(1/320),1,(1/2)] 19065104305674465412139450368000000000000 12592341289704530778556672602086861438976 47593435739583111977974628352000000000000 raw00939 affine00939
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00939_raw leaf00939_rectangular
    leaf00939_transform leaf00939_sign leaf00939_log
#print axioms leaf00939_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
