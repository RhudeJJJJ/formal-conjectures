/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00524 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 980452166561323191854170112000000000000 866569732741910208772156542256221782016 15921972569675261474569715712000000000000))
theorem leaf00524_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 980452166561323191854170112000000000000 866569732741910208772156542256221782016 15921972569675261474569715712000000000000 raw00524=true := by decide +kernel
#print axioms leaf00524_raw
theorem leaf00524_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00524=true := by decide +kernel
#print axioms leaf00524_rectangular
def affine00524 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00524 (IntegerComputedClassCell.leftNumerator ![(47/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(47/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(47/3200),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00524_transform : affine00524=(NestedInteger.clearedAll 3 raw00524 (IntegerComputedClassCell.leftNumerator ![(47/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(47/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(47/3200),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00524_transform
theorem leaf00524_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00524=true := by decide +kernel
#print axioms leaf00524_sign
theorem leaf00524_log : RationalLog.accepts (112504753/134217728) (-378961853/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00524_log
def leaf00524 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (54426028493/1000000000000) (112504753/134217728) (-378961853/4294967296) 1 8 ![60,0,4] ![(47/3200),0,(1/2)] ![(1/3200),1,(1/2)] affine00524
theorem leaf00524_checked : FastNestedCellData.accepts 1 2 4 leaf00524=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (54426028493/1000000000000) (112504753/134217728) (-378961853/4294967296) 1 8 ![60,0,4] ![(47/3200),0,(1/2)] ![(1/3200),1,(1/2)] 980452166561323191854170112000000000000 866569732741910208772156542256221782016 15921972569675261474569715712000000000000 raw00524 affine00524
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00524_raw leaf00524_rectangular
    leaf00524_transform leaf00524_sign leaf00524_log
#print axioms leaf00524_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
