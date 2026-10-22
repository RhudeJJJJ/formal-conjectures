/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00156 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 489277247295030992595448758272000000000000 4073990942609701513004356772633927221248 9599857326854171907204317184000000000000))
theorem leaf00156_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 489277247295030992595448758272000000000000 4073990942609701513004356772633927221248 9599857326854171907204317184000000000000 raw00156=true := by decide +kernel
#print axioms leaf00156_raw
theorem leaf00156_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00156=true := by decide +kernel
#print axioms leaf00156_rectangular
def affine00156 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00156 (IntegerComputedClassCell.leftNumerator ![(67/3200),0,0] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(67/3200),0,0] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(67/3200),0,0] ![(3/6400),1,(1/4)]))
theorem leaf00156_transform : affine00156=(NestedInteger.clearedAll 3 raw00156 (IntegerComputedClassCell.leftNumerator ![(67/3200),0,0] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(67/3200),0,0] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(67/3200),0,0] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00156_transform
theorem leaf00156_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00156=true := by decide +kernel
#print axioms leaf00156_sign
theorem leaf00156_log : RationalLog.accepts (25107237/4294967296) (-11042453733/4294967296) 8 8=true := by decide +kernel
#print axioms leaf00156_log
def leaf00156 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (106095090893/250000000000) (25107237/4294967296) (-11042453733/4294967296) 8 8 ![52,0,4] ![(67/3200),0,0] ![(3/6400),1,(1/4)] affine00156
theorem leaf00156_checked : FastNestedCellData.accepts 1 0 4 leaf00156=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (106095090893/250000000000) (25107237/4294967296) (-11042453733/4294967296) 8 8 ![52,0,4] ![(67/3200),0,0] ![(3/6400),1,(1/4)] 489277247295030992595448758272000000000000 4073990942609701513004356772633927221248 9599857326854171907204317184000000000000 raw00156 affine00156
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00156_raw leaf00156_rectangular
    leaf00156_transform leaf00156_sign leaf00156_log
#print axioms leaf00156_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
