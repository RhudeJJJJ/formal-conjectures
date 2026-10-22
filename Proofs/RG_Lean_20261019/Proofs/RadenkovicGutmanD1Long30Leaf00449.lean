/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00449 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 778941416695317677672367128576000000000000 707399432896953975006002614804350442143744 16752500273896174219235640213504000000000000))
theorem leaf00449_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 778941416695317677672367128576000000000000 707399432896953975006002614804350442143744 16752500273896174219235640213504000000000000 raw00449=true := by decide +kernel
#print axioms leaf00449_raw
theorem leaf00449_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00449=true := by decide +kernel
#print axioms leaf00449_rectangular
def affine00449 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00449 (IntegerComputedClassCell.leftNumerator ![(73/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(73/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(73/6400),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00449_transform : affine00449=(NestedInteger.clearedAll 3 raw00449 (IntegerComputedClassCell.leftNumerator ![(73/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(73/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(73/6400),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00449_transform
theorem leaf00449_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00449=true := by decide +kernel
#print axioms leaf00449_sign
theorem leaf00449_log : RationalLog.accepts (3742464259/4294967296) (-295707791/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00449_log
def leaf00449 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (42226498811/1000000000000) (3742464259/4294967296) (-295707791/4294967296) 1 8 ![60,0,4] ![(73/6400),0,(1/2)] ![(1/6400),1,(1/2)] affine00449
theorem leaf00449_checked : FastNestedCellData.accepts 1 2 4 leaf00449=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (42226498811/1000000000000) (3742464259/4294967296) (-295707791/4294967296) 1 8 ![60,0,4] ![(73/6400),0,(1/2)] ![(1/6400),1,(1/2)] 778941416695317677672367128576000000000000 707399432896953975006002614804350442143744 16752500273896174219235640213504000000000000 raw00449 affine00449
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00449_raw leaf00449_rectangular
    leaf00449_transform leaf00449_sign leaf00449_log
#print axioms leaf00449_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
