/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00053 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 36363734574168742420828651520000000000 35286120928154315000351833712391880704 2796888720907511364518412288000000000000))
theorem leaf00053_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 36363734574168742420828651520000000000 35286120928154315000351833712391880704 2796888720907511364518412288000000000000 raw00053=true := by decide +kernel
#print axioms leaf00053_raw
theorem leaf00053_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00053=true := by decide +kernel
#print axioms leaf00053_rectangular
def affine00053 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00053 (IntegerComputedClassCell.leftNumerator ![(13/8000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/8000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/8000),0,(1/4)] ![(1/16000),1,(1/4)]))
theorem leaf00053_transform : affine00053=(NestedInteger.clearedAll 3 raw00053 (IntegerComputedClassCell.leftNumerator ![(13/8000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/8000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/8000),0,(1/4)] ![(1/16000),1,(1/4)])) := by decide +kernel
#print axioms leaf00053_transform
theorem leaf00053_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00053=true := by decide +kernel
#print axioms leaf00053_sign
theorem leaf00053_log : RationalLog.accepts (2057881825/2147483648) (-91524817/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00053_log
def leaf00053 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (1577025601/125000000000) (2057881825/2147483648) (-91524817/4294967296) 1 8 ![60,0,4] ![(13/8000),0,(1/4)] ![(1/16000),1,(1/4)] affine00053
theorem leaf00053_checked : FastNestedCellData.accepts 1 2 4 leaf00053=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (1577025601/125000000000) (2057881825/2147483648) (-91524817/4294967296) 1 8 ![60,0,4] ![(13/8000),0,(1/4)] ![(1/16000),1,(1/4)] 36363734574168742420828651520000000000 35286120928154315000351833712391880704 2796888720907511364518412288000000000000 raw00053 affine00053
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00053_raw leaf00053_rectangular
    leaf00053_transform leaf00053_sign leaf00053_log
#print axioms leaf00053_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
