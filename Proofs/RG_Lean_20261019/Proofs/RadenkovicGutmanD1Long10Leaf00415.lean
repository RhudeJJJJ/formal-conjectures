/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00415 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 191842255389670750796397307494400000000000 250093202797270202366848231707589736398848 4809582015395740617733092409344000000000000))
theorem leaf00415_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 191842255389670750796397307494400000000000 250093202797270202366848231707589736398848 4809582015395740617733092409344000000000000 raw00415=true := by decide +kernel
#print axioms leaf00415_raw
theorem leaf00415_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00415=true := by decide +kernel
#print axioms leaf00415_rectangular
def affine00415 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00415 (IntegerComputedClassCell.leftNumerator ![(9/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/16),0,(1/2)] ![(1/16),1,(1/4)]))
theorem leaf00415_transform : affine00415=(NestedInteger.clearedAll 3 raw00415 (IntegerComputedClassCell.leftNumerator ![(9/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/16),0,(1/2)] ![(1/16),1,(1/4)])) := by decide +kernel
#print axioms leaf00415_transform
theorem leaf00415_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00415=true := by decide +kernel
#print axioms leaf00415_sign
theorem leaf00415_log : RationalLog.accepts (5322334585/4294967296) (460566733/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00415_log
def leaf00415 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (51998947517/1000000000000) (5322334585/4294967296) (460566733/4294967296) 0 8 ![52,0,4] ![(9/16),0,(1/2)] ![(1/16),1,(1/4)] affine00415
theorem leaf00415_checked : FastNestedCellData.accepts 1 0 4 leaf00415=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (51998947517/1000000000000) (5322334585/4294967296) (460566733/4294967296) 0 8 ![52,0,4] ![(9/16),0,(1/2)] ![(1/16),1,(1/4)] 191842255389670750796397307494400000000000 250093202797270202366848231707589736398848 4809582015395740617733092409344000000000000 raw00415 affine00415
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00415_raw leaf00415_rectangular
    leaf00415_transform leaf00415_sign leaf00415_log
#print axioms leaf00415_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
