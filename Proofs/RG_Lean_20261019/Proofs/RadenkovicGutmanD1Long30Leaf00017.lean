/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00017 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 5466716553576397810220138496000000000000 5224452525960534026793601682115750002688 275457105190358022138502316032000000000000))
theorem leaf00017_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 5466716553576397810220138496000000000000 5224452525960534026793601682115750002688 275457105190358022138502316032000000000000 raw00017=true := by decide +kernel
#print axioms leaf00017_raw
theorem leaf00017_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00017=true := by decide +kernel
#print axioms leaf00017_rectangular
def affine00017 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00017 (IntegerComputedClassCell.leftNumerator ![(19/16000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(19/16000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(19/16000),0,(1/8)] ![(1/16000),1,(1/8)]))
theorem leaf00017_transform : affine00017=(NestedInteger.clearedAll 3 raw00017 (IntegerComputedClassCell.leftNumerator ![(19/16000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(19/16000),0,(1/8)] ![(1/16000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(19/16000),0,(1/8)] ![(1/16000),1,(1/8)])) := by decide +kernel
#print axioms leaf00017_transform
theorem leaf00017_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00017=true := by decide +kernel
#print axioms leaf00017_sign
theorem leaf00017_log : RationalLog.accepts (2014114691/2147483648) (-68845145/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00017_log
def leaf00017 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (4741620771/250000000000) (2014114691/2147483648) (-68845145/2147483648) 1 8 ![60,0,4] ![(19/16000),0,(1/8)] ![(1/16000),1,(1/8)] affine00017
theorem leaf00017_checked : FastNestedCellData.accepts 1 2 4 leaf00017=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (4741620771/250000000000) (2014114691/2147483648) (-68845145/2147483648) 1 8 ![60,0,4] ![(19/16000),0,(1/8)] ![(1/16000),1,(1/8)] 5466716553576397810220138496000000000000 5224452525960534026793601682115750002688 275457105190358022138502316032000000000000 raw00017 affine00017
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00017_raw leaf00017_rectangular
    leaf00017_transform leaf00017_sign leaf00017_log
#print axioms leaf00017_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
