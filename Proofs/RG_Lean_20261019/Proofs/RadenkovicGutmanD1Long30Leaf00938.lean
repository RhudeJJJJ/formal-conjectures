/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00938 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 7956836154610581951744837681152000000000000 4239139977530010063678212655129592024006656 9827817079382110801922724200448000000000000))
theorem leaf00938_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 7956836154610581951744837681152000000000000 4239139977530010063678212655129592024006656 9827817079382110801922724200448000000000000 raw00938=true := by decide +kernel
#print axioms leaf00938_raw
theorem leaf00938_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00938=true := by decide +kernel
#print axioms leaf00938_rectangular
def affine00938 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00938 (IntegerComputedClassCell.leftNumerator ![(7/80),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/80),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/80),0,(1/4)] ![(1/320),1,(1/4)]))
theorem leaf00938_transform : affine00938=(NestedInteger.clearedAll 3 raw00938 (IntegerComputedClassCell.leftNumerator ![(7/80),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/80),0,(1/4)] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/80),0,(1/4)] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00938_transform
theorem leaf00938_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00938=true := by decide +kernel
#print axioms leaf00938_sign
theorem leaf00938_log : RationalLog.accepts (1598652629/4294967296) (-1061160583/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00938_log
def leaf00938 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (431340952247/1000000000000) (1598652629/4294967296) (-1061160583/2147483648) 2 8 ![60,0,4] ![(7/80),0,(1/4)] ![(1/320),1,(1/4)] affine00938
theorem leaf00938_checked : FastNestedCellData.accepts 1 2 4 leaf00938=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (431340952247/1000000000000) (1598652629/4294967296) (-1061160583/2147483648) 2 8 ![60,0,4] ![(7/80),0,(1/4)] ![(1/320),1,(1/4)] 7956836154610581951744837681152000000000000 4239139977530010063678212655129592024006656 9827817079382110801922724200448000000000000 raw00938 affine00938
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00938_raw leaf00938_rectangular
    leaf00938_transform leaf00938_sign leaf00938_log
#print axioms leaf00938_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
