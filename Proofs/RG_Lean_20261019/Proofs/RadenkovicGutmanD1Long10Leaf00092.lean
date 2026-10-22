/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00092 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 658590817230212335378110611456000000000000 605299752333502305465803882601771555618816 16954092476015880687561606168576000000000000))
theorem leaf00092_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 658590817230212335378110611456000000000000 605299752333502305465803882601771555618816 16954092476015880687561606168576000000000000 raw00092=true := by decide +kernel
#print axioms leaf00092_raw
theorem leaf00092_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00092=true := by decide +kernel
#print axioms leaf00092_rectangular
def affine00092 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00092 (IntegerComputedClassCell.leftNumerator ![(31/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(31/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(31/3200),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00092_transform : affine00092=(NestedInteger.clearedAll 3 raw00092 (IntegerComputedClassCell.leftNumerator ![(31/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(31/3200),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(31/3200),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00092_transform
theorem leaf00092_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00092=true := by decide +kernel
#print axioms leaf00092_sign
theorem leaf00092_log : RationalLog.accepts (3811358091/4294967296) (-256534913/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00092_log
def leaf00092 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (35702279741/1000000000000) (3811358091/4294967296) (-256534913/4294967296) 1 8 ![52,0,4] ![(31/3200),0,(1/2)] ![(1/3200),1,(1/2)] affine00092
theorem leaf00092_checked : FastNestedCellData.accepts 1 0 4 leaf00092=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (35702279741/1000000000000) (3811358091/4294967296) (-256534913/4294967296) 1 8 ![52,0,4] ![(31/3200),0,(1/2)] ![(1/3200),1,(1/2)] 658590817230212335378110611456000000000000 605299752333502305465803882601771555618816 16954092476015880687561606168576000000000000 raw00092 affine00092
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00092_raw leaf00092_rectangular
    leaf00092_transform leaf00092_sign leaf00092_log
#print axioms leaf00092_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
