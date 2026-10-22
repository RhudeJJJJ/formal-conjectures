/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00683 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 11297279275513774583655379763200000000000 7519587230736085629773313640492437602304 38369830525803358831389966336000000000000))
theorem leaf00683_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 11297279275513774583655379763200000000000 7519587230736085629773313640492437602304 38369830525803358831389966336000000000000 raw00683=true := by decide +kernel
#print axioms leaf00683_raw
theorem leaf00683_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00683=true := by decide +kernel
#print axioms leaf00683_rectangular
def affine00683 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00683 (IntegerComputedClassCell.leftNumerator ![(173/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(173/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(173/6400),0,(1/4)] ![(3/6400),1,(1/4)]))
theorem leaf00683_transform : affine00683=(NestedInteger.clearedAll 3 raw00683 (IntegerComputedClassCell.leftNumerator ![(173/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(173/6400),0,(1/4)] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(173/6400),0,(1/4)] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00683_transform
theorem leaf00683_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00683=true := by decide +kernel
#print axioms leaf00683_sign
theorem leaf00683_log : RationalLog.accepts (298790885/536870912) (-314613735/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00683_log
def leaf00683 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (195976555739/1000000000000) (298790885/536870912) (-314613735/1073741824) 1 8 ![60,0,4] ![(173/6400),0,(1/4)] ![(3/6400),1,(1/4)] affine00683
theorem leaf00683_checked : FastNestedCellData.accepts 1 2 4 leaf00683=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (195976555739/1000000000000) (298790885/536870912) (-314613735/1073741824) 1 8 ![60,0,4] ![(173/6400),0,(1/4)] ![(3/6400),1,(1/4)] 11297279275513774583655379763200000000000 7519587230736085629773313640492437602304 38369830525803358831389966336000000000000 raw00683 affine00683
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00683_raw leaf00683_rectangular
    leaf00683_transform leaf00683_sign leaf00683_log
#print axioms leaf00683_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
