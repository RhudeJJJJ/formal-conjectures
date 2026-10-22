/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00692 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1079747846264255254626723430400000000000 505165675346664421904290162330853965824 1348500884978544683428243046400000000000))
theorem leaf00692_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1079747846264255254626723430400000000000 505165675346664421904290162330853965824 1348500884978544683428243046400000000000 raw00692=true := by decide +kernel
#print axioms leaf00692_raw
theorem leaf00692_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00692=true := by decide +kernel
#print axioms leaf00692_rectangular
def affine00692 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00692 (IntegerComputedClassCell.leftNumerator ![(179/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(179/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(179/6400),0,(1/8)] ![(3/6400),1,(1/8)]))
theorem leaf00692_transform : affine00692=(NestedInteger.clearedAll 3 raw00692 (IntegerComputedClassCell.leftNumerator ![(179/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(179/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(179/6400),0,(1/8)] ![(3/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00692_transform
theorem leaf00692_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00692=true := by decide +kernel
#print axioms leaf00692_sign
theorem leaf00692_log : RationalLog.accepts (182726267/536870912) (-1157245101/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00692_log
def leaf00692 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (37461278741/100000000000) (182726267/536870912) (-1157245101/2147483648) 2 8 ![60,0,4] ![(179/6400),0,(1/8)] ![(3/6400),1,(1/8)] affine00692
theorem leaf00692_checked : FastNestedCellData.accepts 1 2 4 leaf00692=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (37461278741/100000000000) (182726267/536870912) (-1157245101/2147483648) 2 8 ![60,0,4] ![(179/6400),0,(1/8)] ![(3/6400),1,(1/8)] 1079747846264255254626723430400000000000 505165675346664421904290162330853965824 1348500884978544683428243046400000000000 raw00692 affine00692
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00692_raw leaf00692_rectangular
    leaf00692_transform leaf00692_sign leaf00692_log
#print axioms leaf00692_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
