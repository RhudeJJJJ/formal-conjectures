/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00013 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 73156680869001346236771467264000000000000 70297954917639810980951983049389822181376 4431476277583393648159947227136000000000000))
theorem leaf00013_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 73156680869001346236771467264000000000000 70297954917639810980951983049389822181376 4431476277583393648159947227136000000000000 raw00013=true := by decide +kernel
#print axioms leaf00013_raw
theorem leaf00013_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00013=true := by decide +kernel
#print axioms leaf00013_rectangular
def affine00013 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00013 (IntegerComputedClassCell.leftNumerator ![(1/500),0,(1/4)] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/500),0,(1/4)] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/500),0,(1/4)] ![(3/16000),1,(1/4)]))
theorem leaf00013_transform : affine00013=(NestedInteger.clearedAll 3 raw00013 (IntegerComputedClassCell.leftNumerator ![(1/500),0,(1/4)] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/500),0,(1/4)] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/500),0,(1/4)] ![(3/16000),1,(1/4)])) := by decide +kernel
#print axioms leaf00013_transform
theorem leaf00013_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00013=true := by decide +kernel
#print axioms leaf00013_sign
theorem leaf00013_log : RationalLog.accepts (4062686179/4294967296) (-59699597/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00013_log
def leaf00013 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (7931663233/500000000000) (4062686179/4294967296) (-59699597/2147483648) 1 8 ![52,0,4] ![(1/500),0,(1/4)] ![(3/16000),1,(1/4)] affine00013
theorem leaf00013_checked : FastNestedCellData.accepts 1 0 4 leaf00013=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (7931663233/500000000000) (4062686179/4294967296) (-59699597/2147483648) 1 8 ![52,0,4] ![(1/500),0,(1/4)] ![(3/16000),1,(1/4)] 73156680869001346236771467264000000000000 70297954917639810980951983049389822181376 4431476277583393648159947227136000000000000 raw00013 affine00013
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00013_raw leaf00013_rectangular
    leaf00013_transform leaf00013_sign leaf00013_log
#print axioms leaf00013_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
