/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00645 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 987382859085086986757331746816000000000000 20580133525260337545279087699155428048896 24030474390591260500590329856000000000000))
theorem leaf00645_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 987382859085086986757331746816000000000000 20580133525260337545279087699155428048896 24030474390591260500590329856000000000000 raw00645=true := by decide +kernel
#print axioms leaf00645_raw
theorem leaf00645_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00645=true := by decide +kernel
#print axioms leaf00645_rectangular
def affine00645 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00645 (IntegerComputedClassCell.leftNumerator ![(19/800),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/800),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/800),0,0] ![(3/6400),1,(1/16)]))
theorem leaf00645_transform : affine00645=(NestedInteger.clearedAll 3 raw00645 (IntegerComputedClassCell.leftNumerator ![(19/800),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/800),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/800),0,0] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00645_transform
theorem leaf00645_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00645=true := by decide +kernel
#print axioms leaf00645_sign
theorem leaf00645_log : RationalLog.accepts (48222161/4294967296) (-9640871531/4294967296) 7 8=true := by decide +kernel
#print axioms leaf00645_log
def leaf00645 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (214104528179/250000000000) (48222161/4294967296) (-9640871531/4294967296) 7 8 ![60,0,4] ![(19/800),0,0] ![(3/6400),1,(1/16)] affine00645
theorem leaf00645_checked : FastNestedCellData.accepts 1 2 4 leaf00645=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (214104528179/250000000000) (48222161/4294967296) (-9640871531/4294967296) 7 8 ![60,0,4] ![(19/800),0,0] ![(3/6400),1,(1/16)] 987382859085086986757331746816000000000000 20580133525260337545279087699155428048896 24030474390591260500590329856000000000000 raw00645 affine00645
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00645_raw leaf00645_rectangular
    leaf00645_transform leaf00645_sign leaf00645_log
#print axioms leaf00645_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
