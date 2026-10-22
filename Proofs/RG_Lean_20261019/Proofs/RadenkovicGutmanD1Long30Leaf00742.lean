/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00742 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 120035101461775549739235803136000000000000 52582568290116345020607463297896136310784 126262178752017856375539367936000000000000))
theorem leaf00742_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 120035101461775549739235803136000000000000 52582568290116345020607463297896136310784 126262178752017856375539367936000000000000 raw00742=true := by decide +kernel
#print axioms leaf00742_raw
theorem leaf00742_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00742=true := by decide +kernel
#print axioms leaf00742_rectangular
def affine00742 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00742 (IntegerComputedClassCell.leftNumerator ![(209/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(209/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(209/6400),0,(1/8)] ![(3/6400),1,(1/8)]))
theorem leaf00742_transform : affine00742=(NestedInteger.clearedAll 3 raw00742 (IntegerComputedClassCell.leftNumerator ![(209/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(209/6400),0,(1/8)] ![(3/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(209/6400),0,(1/8)] ![(3/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00742_transform
theorem leaf00742_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00742=true := by decide +kernel
#print axioms leaf00742_sign
theorem leaf00742_log : RationalLog.accepts (332070649/1073741824) (-78756087/134217728) 2 8=true := by decide +kernel
#print axioms leaf00742_log
def leaf00742 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (208227708447/500000000000) (332070649/1073741824) (-78756087/134217728) 2 8 ![60,0,4] ![(209/6400),0,(1/8)] ![(3/6400),1,(1/8)] affine00742
theorem leaf00742_checked : FastNestedCellData.accepts 1 2 4 leaf00742=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (208227708447/500000000000) (332070649/1073741824) (-78756087/134217728) 2 8 ![60,0,4] ![(209/6400),0,(1/8)] ![(3/6400),1,(1/8)] 120035101461775549739235803136000000000000 52582568290116345020607463297896136310784 126262178752017856375539367936000000000000 raw00742 affine00742
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00742_raw leaf00742_rectangular
    leaf00742_transform leaf00742_sign leaf00742_log
#print axioms leaf00742_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
