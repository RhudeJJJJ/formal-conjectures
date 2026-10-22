/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00435 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 1917190077414081878984071577600000000000 2154173041154374279891842027282902286336 207269374324414921278056143257600000000000))
theorem leaf00435_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 1917190077414081878984071577600000000000 2154173041154374279891842027282902286336 207269374324414921278056143257600000000000 raw00435=true := by decide +kernel
#print axioms leaf00435_raw
theorem leaf00435_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00435=true := by decide +kernel
#print axioms leaf00435_rectangular
def affine00435 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00435 (IntegerComputedClassCell.leftNumerator ![(9/32),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/32),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/32),0,0] ![(1/32),1,(1/2)]))
theorem leaf00435_transform : affine00435=(NestedInteger.clearedAll 3 raw00435 (IntegerComputedClassCell.leftNumerator ![(9/32),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(9/32),0,0] ![(1/32),1,(1/2)]) (IntegerComputedClassCell.denominator ![(9/32),0,0] ![(1/32),1,(1/2)])) := by decide +kernel
#print axioms leaf00435_transform
theorem leaf00435_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00435=true := by decide +kernel
#print axioms leaf00435_sign
theorem leaf00435_log : RationalLog.accepts (2388113173/2147483648) (114038711/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00435_log
def leaf00435 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (2078621647/200000000000) (2388113173/2147483648) (114038711/2147483648) 0 8 ![52,0,4] ![(9/32),0,0] ![(1/32),1,(1/2)] affine00435
theorem leaf00435_checked : FastNestedCellData.accepts 1 0 4 leaf00435=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (2078621647/200000000000) (2388113173/2147483648) (114038711/2147483648) 0 8 ![52,0,4] ![(9/32),0,0] ![(1/32),1,(1/2)] 1917190077414081878984071577600000000000 2154173041154374279891842027282902286336 207269374324414921278056143257600000000000 raw00435 affine00435
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00435_raw leaf00435_rectangular
    leaf00435_transform leaf00435_sign leaf00435_log
#print axioms leaf00435_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
