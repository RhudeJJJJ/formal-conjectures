/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00963 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 415850490935100933155880488140800000000000 228302558572898135429051189905416542748672 506364542205697214503580598272000000000000))
theorem leaf00963_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 415850490935100933155880488140800000000000 228302558572898135429051189905416542748672 506364542205697214503580598272000000000000 raw00963=true := by decide +kernel
#print axioms leaf00963_raw
theorem leaf00963_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00963=true := by decide +kernel
#print axioms leaf00963_rectangular
def affine00963 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00963 (IntegerComputedClassCell.leftNumerator ![(33/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(33/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(33/320),0,(1/4)] ![(1/320),1,(1/4)]))
theorem leaf00963_transform : affine00963=(NestedInteger.clearedAll 3 raw00963 (IntegerComputedClassCell.leftNumerator ![(33/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(33/320),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(33/320),0,(1/4)] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00963_transform
theorem leaf00963_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00963=true := by decide +kernel
#print axioms leaf00963_sign
theorem leaf00963_log : RationalLog.accepts (812598695/2147483648) (-1043478083/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00963_log
def leaf00963 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (450866005701/1000000000000) (812598695/2147483648) (-1043478083/2147483648) 2 8 ![60,0,4] ![(33/320),0,(1/4)] ![(1/320),1,(1/4)] affine00963
theorem leaf00963_checked : FastNestedCellData.accepts 1 2 4 leaf00963=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (450866005701/1000000000000) (812598695/2147483648) (-1043478083/2147483648) 2 8 ![60,0,4] ![(33/320),0,(1/4)] ![(1/320),1,(1/4)] 415850490935100933155880488140800000000000 228302558572898135429051189905416542748672 506364542205697214503580598272000000000000 raw00963 affine00963
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00963_raw leaf00963_rectangular
    leaf00963_transform leaf00963_sign leaf00963_log
#print axioms leaf00963_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
