/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00389 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 163146324328514383520796246016000000000000 150383093822636878777704064604502583410688 4250905523272623498603236687872000000000000))
theorem leaf00389_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 163146324328514383520796246016000000000000 150383093822636878777704064604502583410688 4250905523272623498603236687872000000000000 raw00389=true := by decide +kernel
#print axioms leaf00389_raw
theorem leaf00389_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00389=true := by decide +kernel
#print axioms leaf00389_rectangular
def affine00389 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00389 (IntegerComputedClassCell.leftNumerator ![(61/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(61/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(61/6400),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00389_transform : affine00389=(NestedInteger.clearedAll 3 raw00389 (IntegerComputedClassCell.leftNumerator ![(61/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(61/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(61/6400),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00389_transform
theorem leaf00389_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00389=true := by decide +kernel
#print axioms leaf00389_sign
theorem leaf00389_log : RationalLog.accepts (3823694507/4294967296) (-62398817/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00389_log
def leaf00389 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (17688359927/500000000000) (3823694507/4294967296) (-62398817/1073741824) 1 8 ![60,0,4] ![(61/6400),0,(1/2)] ![(1/6400),1,(1/2)] affine00389
theorem leaf00389_checked : FastNestedCellData.accepts 1 2 4 leaf00389=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (17688359927/500000000000) (3823694507/4294967296) (-62398817/1073741824) 1 8 ![60,0,4] ![(61/6400),0,(1/2)] ![(1/6400),1,(1/2)] 163146324328514383520796246016000000000000 150383093822636878777704064604502583410688 4250905523272623498603236687872000000000000 raw00389 affine00389
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00389_raw leaf00389_rectangular
    leaf00389_transform leaf00389_sign leaf00389_log
#print axioms leaf00389_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
