/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00160 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 731552546100994155874579644416000000000000 519695568535734446116400345216307802669056 3276145780680595568084662616064000000000000))
theorem leaf00160_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 731552546100994155874579644416000000000000 519695568535734446116400345216307802669056 3276145780680595568084662616064000000000000 raw00160=true := by decide +kernel
#print axioms leaf00160_raw
theorem leaf00160_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00160=true := by decide +kernel
#print axioms leaf00160_rectangular
def affine00160 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00160 (IntegerComputedClassCell.leftNumerator ![(137/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(137/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(137/6400),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00160_transform : affine00160=(NestedInteger.clearedAll 3 raw00160 (IntegerComputedClassCell.leftNumerator ![(137/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(137/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(137/6400),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00160_transform
theorem leaf00160_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00160=true := by decide +kernel
#print axioms leaf00160_sign
theorem leaf00160_log : RationalLog.accepts (2633410209/4294967296) (-525236161/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00160_log
def leaf00160 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (79315085977/500000000000) (2633410209/4294967296) (-525236161/2147483648) 1 8 ![52,0,4] ![(137/6400),0,(1/4)] ![(3/6400),1,(1/4)] affine00160
theorem leaf00160_checked : FastNestedCellData.accepts 1 0 4 leaf00160=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (79315085977/500000000000) (2633410209/4294967296) (-525236161/2147483648) 1 8 ![52,0,4] ![(137/6400),0,(1/4)] ![(3/6400),1,(1/4)] 731552546100994155874579644416000000000000 519695568535734446116400345216307802669056 3276145780680595568084662616064000000000000 raw00160 affine00160
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00160_raw leaf00160_rectangular
    leaf00160_transform leaf00160_sign leaf00160_log
#print axioms leaf00160_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
