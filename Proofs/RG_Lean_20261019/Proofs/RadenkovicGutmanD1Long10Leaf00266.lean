/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00266 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 3522712170170516520280682135552000000000000 2453377055790935724188195813623206380568576 12847151989228736760280365662208000000000000))
theorem leaf00266_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 3522712170170516520280682135552000000000000 2453377055790935724188195813623206380568576 12847151989228736760280365662208000000000000 raw00266=true := by decide +kernel
#print axioms leaf00266_raw
theorem leaf00266_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00266=true := by decide +kernel
#print axioms leaf00266_rectangular
def affine00266 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00266 (IntegerComputedClassCell.leftNumerator ![(9/160),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/160),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/160),0,(1/2)] ![(1/640),1,(1/2)]))
theorem leaf00266_transform : affine00266=(NestedInteger.clearedAll 3 raw00266 (IntegerComputedClassCell.leftNumerator ![(9/160),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/160),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/160),0,(1/2)] ![(1/640),1,(1/2)])) := by decide +kernel
#print axioms leaf00266_transform
theorem leaf00266_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00266=true := by decide +kernel
#print axioms leaf00266_sign
theorem leaf00266_log : RationalLog.accepts (2511582309/4294967296) (-18002993/67108864) 1 8=true := by decide +kernel
#print axioms leaf00266_log
def leaf00266 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (190966609397/1000000000000) (2511582309/4294967296) (-18002993/67108864) 1 8 ![52,0,4] ![(9/160),0,(1/2)] ![(1/640),1,(1/2)] affine00266
theorem leaf00266_checked : FastNestedCellData.accepts 1 0 4 leaf00266=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (190966609397/1000000000000) (2511582309/4294967296) (-18002993/67108864) 1 8 ![52,0,4] ![(9/160),0,(1/2)] ![(1/640),1,(1/2)] 3522712170170516520280682135552000000000000 2453377055790935724188195813623206380568576 12847151989228736760280365662208000000000000 raw00266 affine00266
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00266_raw leaf00266_rectangular
    leaf00266_transform leaf00266_sign leaf00266_log
#print axioms leaf00266_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
