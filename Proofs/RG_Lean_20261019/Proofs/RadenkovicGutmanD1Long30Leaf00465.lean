/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00465 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 278736887400297520567704092672000000000000 1370305211139700064469625622652971384832 1889301843676132700168650752000000000000))
theorem leaf00465_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 278736887400297520567704092672000000000000 1370305211139700064469625622652971384832 1889301843676132700168650752000000000000 raw00465=true := by decide +kernel
#print axioms leaf00465_raw
theorem leaf00465_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00465=true := by decide +kernel
#print axioms leaf00465_rectangular
def affine00465 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00465 (IntegerComputedClassCell.leftNumerator ![(77/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(77/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(77/6400),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00465_transform : affine00465=(NestedInteger.clearedAll 3 raw00465 (IntegerComputedClassCell.leftNumerator ![(77/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(77/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(77/6400),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00465_transform
theorem leaf00465_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00465=true := by decide +kernel
#print axioms leaf00465_sign
theorem leaf00465_log : RationalLog.accepts (3059559/1073741824) (-1573202019/536870912) 9 8=true := by decide +kernel
#print axioms leaf00465_log
def leaf00465 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (725297133291/1000000000000) (3059559/1073741824) (-1573202019/536870912) 9 8 ![60,0,4] ![(77/6400),0,0] ![(1/6400),1,(1/16)] affine00465
theorem leaf00465_checked : FastNestedCellData.accepts 1 2 4 leaf00465=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (725297133291/1000000000000) (3059559/1073741824) (-1573202019/536870912) 9 8 ![60,0,4] ![(77/6400),0,0] ![(1/6400),1,(1/16)] 278736887400297520567704092672000000000000 1370305211139700064469625622652971384832 1889301843676132700168650752000000000000 raw00465 affine00465
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00465_raw leaf00465_rectangular
    leaf00465_transform leaf00465_sign leaf00465_log
#print axioms leaf00465_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
