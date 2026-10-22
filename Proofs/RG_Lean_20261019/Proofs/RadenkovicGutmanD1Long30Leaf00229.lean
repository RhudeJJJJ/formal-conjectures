/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00229 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 377159312513245436892204236800000000000 361897812983753242992081198424761827328 20581754537813881704652210176000000000000))
theorem leaf00229_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 377159312513245436892204236800000000000 361897812983753242992081198424761827328 20581754537813881704652210176000000000000 raw00229=true := by decide +kernel
#print axioms leaf00229_raw
theorem leaf00229_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00229=true := by decide +kernel
#print axioms leaf00229_rectangular
def affine00229 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00229 (IntegerComputedClassCell.leftNumerator ![(151/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(151/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(151/32000),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00229_transform : affine00229=(NestedInteger.clearedAll 3 raw00229 (IntegerComputedClassCell.leftNumerator ![(151/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(151/32000),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(151/32000),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00229_transform
theorem leaf00229_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00229=true := by decide +kernel
#print axioms leaf00229_sign
theorem leaf00229_log : RationalLog.accepts (4049962095/4294967296) (-7883471/268435456) 1 8=true := by decide +kernel
#print axioms leaf00229_log
def leaf00229 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (8791714339/500000000000) (4049962095/4294967296) (-7883471/268435456) 1 8 ![60,0,4] ![(151/32000),0,(1/2)] ![(3/32000),1,(1/2)] affine00229
theorem leaf00229_checked : FastNestedCellData.accepts 1 2 4 leaf00229=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (8791714339/500000000000) (4049962095/4294967296) (-7883471/268435456) 1 8 ![60,0,4] ![(151/32000),0,(1/2)] ![(3/32000),1,(1/2)] 377159312513245436892204236800000000000 361897812983753242992081198424761827328 20581754537813881704652210176000000000000 raw00229 affine00229
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00229_raw leaf00229_rectangular
    leaf00229_transform leaf00229_sign leaf00229_log
#print axioms leaf00229_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
