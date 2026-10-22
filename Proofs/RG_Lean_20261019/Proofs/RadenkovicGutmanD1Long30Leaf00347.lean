/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00347 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 9229556853137358614217883648000000000000 6934179852734306439845155557393613979648 54136978054852163192735399936000000000000))
theorem leaf00347_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 9229556853137358614217883648000000000000 6934179852734306439845155557393613979648 54136978054852163192735399936000000000000 raw00347=true := by decide +kernel
#print axioms leaf00347_raw
theorem leaf00347_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00347=true := by decide +kernel
#print axioms leaf00347_rectangular
def affine00347 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00347 (IntegerComputedClassCell.leftNumerator ![(53/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(53/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(53/6400),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00347_transform : affine00347=(NestedInteger.clearedAll 3 raw00347 (IntegerComputedClassCell.leftNumerator ![(53/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(53/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(53/6400),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00347_transform
theorem leaf00347_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00347=true := by decide +kernel
#print axioms leaf00347_sign
theorem leaf00347_log : RationalLog.accepts (2860434247/4294967296) (-872888773/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00347_log
def leaf00347 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (8005364473/62500000000) (2860434247/4294967296) (-872888773/4294967296) 1 8 ![60,0,4] ![(53/6400),0,(1/8)] ![(1/6400),1,(1/8)] affine00347
theorem leaf00347_checked : FastNestedCellData.accepts 1 2 4 leaf00347=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (8005364473/62500000000) (2860434247/4294967296) (-872888773/4294967296) 1 8 ![60,0,4] ![(53/6400),0,(1/8)] ![(1/6400),1,(1/8)] 9229556853137358614217883648000000000000 6934179852734306439845155557393613979648 54136978054852163192735399936000000000000 raw00347 affine00347
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00347_raw leaf00347_rectangular
    leaf00347_transform leaf00347_sign leaf00347_log
#print axioms leaf00347_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
