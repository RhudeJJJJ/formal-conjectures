/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00376 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 105987015470849687655565754368000000000000 110137260468852316964267588880417901510656 299516916031920599999969230848000000000000))
theorem leaf00376_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 105987015470849687655565754368000000000000 110137260468852316964267588880417901510656 299516916031920599999969230848000000000000 raw00376=true := by decide +kernel
#print axioms leaf00376_raw
theorem leaf00376_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00376=true := by decide +kernel
#print axioms leaf00376_rectangular
def affine00376 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00376 (IntegerComputedClassCell.leftNumerator ![(7/20),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/20),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/20),0,(1/4)] ![(3/80),1,(1/4)]))
theorem leaf00376_transform : affine00376=(NestedInteger.clearedAll 3 raw00376 (IntegerComputedClassCell.leftNumerator ![(7/20),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/20),0,(1/4)] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/20),0,(1/4)] ![(3/80),1,(1/4)])) := by decide +kernel
#print axioms leaf00376_transform
theorem leaf00376_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00376=true := by decide +kernel
#print axioms leaf00376_sign
theorem leaf00376_log : RationalLog.accepts (1631606553/2147483648) (-73747711/536870912) 1 8=true := by decide +kernel
#print axioms leaf00376_log
def leaf00376 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (91929081943/250000000000) (1631606553/2147483648) (-73747711/536870912) 1 8 ![52,0,4] ![(7/20),0,(1/4)] ![(3/80),1,(1/4)] affine00376
theorem leaf00376_checked : FastNestedCellData.accepts 1 0 4 leaf00376=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (91929081943/250000000000) (1631606553/2147483648) (-73747711/536870912) 1 8 ![52,0,4] ![(7/20),0,(1/4)] ![(3/80),1,(1/4)] 105987015470849687655565754368000000000000 110137260468852316964267588880417901510656 299516916031920599999969230848000000000000 raw00376 affine00376
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00376_raw leaf00376_rectangular
    leaf00376_transform leaf00376_sign leaf00376_log
#print axioms leaf00376_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
