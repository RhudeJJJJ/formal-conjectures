/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00834 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 154053753983999784281261159219200000000000 111270954061640402506830929568240198746112 666191754283948540598459301888000000000000))
theorem leaf00834_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 154053753983999784281261159219200000000000 111270954061640402506830929568240198746112 666191754283948540598459301888000000000000 raw00834=true := by decide +kernel
#print axioms leaf00834_raw
theorem leaf00834_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00834=true := by decide +kernel
#print axioms leaf00834_rectangular
def affine00834 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00834 (IntegerComputedClassCell.leftNumerator ![(77/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(77/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(77/1600),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00834_transform : affine00834=(NestedInteger.clearedAll 3 raw00834 (IntegerComputedClassCell.leftNumerator ![(77/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(77/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(77/1600),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00834_transform
theorem leaf00834_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00834=true := by decide +kernel
#print axioms leaf00834_sign
theorem leaf00834_log : RationalLog.accepts (1329104345/2147483648) (-257586093/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00834_log
def leaf00834 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (167025414749/1000000000000) (1329104345/2147483648) (-257586093/1073741824) 1 8 ![60,0,4] ![(77/1600),0,(1/2)] ![(3/3200),1,(1/2)] affine00834
theorem leaf00834_checked : FastNestedCellData.accepts 1 2 4 leaf00834=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (167025414749/1000000000000) (1329104345/2147483648) (-257586093/1073741824) 1 8 ![60,0,4] ![(77/1600),0,(1/2)] ![(3/3200),1,(1/2)] 154053753983999784281261159219200000000000 111270954061640402506830929568240198746112 666191754283948540598459301888000000000000 raw00834 affine00834
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00834_raw leaf00834_rectangular
    leaf00834_transform leaf00834_sign leaf00834_log
#print axioms leaf00834_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
