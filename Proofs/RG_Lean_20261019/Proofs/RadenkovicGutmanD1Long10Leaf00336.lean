/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00336 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 194296327263173728084328185856000000000000 70971459974730350431357953189662756438016 105283156365817057391708995584000000000000))
theorem leaf00336_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 194296327263173728084328185856000000000000 70971459974730350431357953189662756438016 105283156365817057391708995584000000000000 raw00336=true := by decide +kernel
#print axioms leaf00336_raw
theorem leaf00336_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00336=true := by decide +kernel
#print axioms leaf00336_rectangular
def affine00336 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00336 (IntegerComputedClassCell.leftNumerator ![(21/160),0,0] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(21/160),0,0] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(21/160),0,0] ![(1/160),1,(1/4)]))
theorem leaf00336_transform : affine00336=(NestedInteger.clearedAll 3 raw00336 (IntegerComputedClassCell.leftNumerator ![(21/160),0,0] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(21/160),0,0] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(21/160),0,0] ![(1/160),1,(1/4)])) := by decide +kernel
#print axioms leaf00336_transform
theorem leaf00336_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00336=true := by decide +kernel
#print axioms leaf00336_sign
theorem leaf00336_log : RationalLog.accepts (117140593/536870912) (-817323077/1073741824) 3 8=true := by decide +kernel
#print axioms leaf00336_log
def leaf00336 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (674100800399/1000000000000) (117140593/536870912) (-817323077/1073741824) 3 8 ![52,0,4] ![(21/160),0,0] ![(1/160),1,(1/4)] affine00336
theorem leaf00336_checked : FastNestedCellData.accepts 1 0 4 leaf00336=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (674100800399/1000000000000) (117140593/536870912) (-817323077/1073741824) 3 8 ![52,0,4] ![(21/160),0,0] ![(1/160),1,(1/4)] 194296327263173728084328185856000000000000 70971459974730350431357953189662756438016 105283156365817057391708995584000000000000 raw00336 affine00336
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00336_raw leaf00336_rectangular
    leaf00336_transform leaf00336_sign leaf00336_log
#print axioms leaf00336_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
