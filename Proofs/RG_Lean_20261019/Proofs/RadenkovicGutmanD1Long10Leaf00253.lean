/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00253 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 301102048213581350862282188390400000000000 163917418621535386278445222074745438076928 502112604094565610678812409856000000000000))
theorem leaf00253_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 301102048213581350862282188390400000000000 163917418621535386278445222074745438076928 502112604094565610678812409856000000000000 raw00253=true := by decide +kernel
#print axioms leaf00253_raw
theorem leaf00253_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00253=true := by decide +kernel
#print axioms leaf00253_rectangular
def affine00253 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00253 (IntegerComputedClassCell.leftNumerator ![(1/20),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/20),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/20),0,(1/4)] ![(1/640),1,(1/4)]))
theorem leaf00253_transform : affine00253=(NestedInteger.clearedAll 3 raw00253 (IntegerComputedClassCell.leftNumerator ![(1/20),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/20),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/20),0,(1/4)] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00253_transform
theorem leaf00253_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00253=true := by decide +kernel
#print axioms leaf00253_sign
theorem leaf00253_log : RationalLog.accepts (881350345/2147483648) (-956271095/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00253_log
def leaf00253 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (326455494813/1000000000000) (881350345/2147483648) (-956271095/2147483648) 2 8 ![52,0,4] ![(1/20),0,(1/4)] ![(1/640),1,(1/4)] affine00253
theorem leaf00253_checked : FastNestedCellData.accepts 1 0 4 leaf00253=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (326455494813/1000000000000) (881350345/2147483648) (-956271095/2147483648) 2 8 ![52,0,4] ![(1/20),0,(1/4)] ![(1/640),1,(1/4)] 301102048213581350862282188390400000000000 163917418621535386278445222074745438076928 502112604094565610678812409856000000000000 raw00253 affine00253
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00253_raw leaf00253_rectangular
    leaf00253_transform leaf00253_sign leaf00253_log
#print axioms leaf00253_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
