/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00219 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 544904439156496385140221542400000000000 19404379143578959928108809705192685568 32075185445600591026847744000000000000))
theorem leaf00219_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 544904439156496385140221542400000000000 19404379143578959928108809705192685568 32075185445600591026847744000000000000 raw00219=true := by decide +kernel
#print axioms leaf00219_raw
theorem leaf00219_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00219=true := by decide +kernel
#print axioms leaf00219_rectangular
def affine00219 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00219 (IntegerComputedClassCell.leftNumerator ![(31/800),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/800),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/800),0,0] ![(3/3200),1,(1/4)]))
theorem leaf00219_transform : affine00219=(NestedInteger.clearedAll 3 raw00219 (IntegerComputedClassCell.leftNumerator ![(31/800),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/800),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/800),0,0] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00219_transform
theorem leaf00219_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00219=true := by decide +kernel
#print axioms leaf00219_sign
theorem leaf00219_log : RationalLog.accepts (5955985/268435456) (-8178077293/4294967296) 6 8=true := by decide +kernel
#print axioms leaf00219_log
def leaf00219 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (151241363643/250000000000) (5955985/268435456) (-8178077293/4294967296) 6 8 ![52,0,4] ![(31/800),0,0] ![(3/3200),1,(1/4)] affine00219
theorem leaf00219_checked : FastNestedCellData.accepts 1 0 4 leaf00219=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (151241363643/250000000000) (5955985/268435456) (-8178077293/4294967296) 6 8 ![52,0,4] ![(31/800),0,0] ![(3/3200),1,(1/4)] 544904439156496385140221542400000000000 19404379143578959928108809705192685568 32075185445600591026847744000000000000 raw00219 affine00219
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00219_raw leaf00219_rectangular
    leaf00219_transform leaf00219_sign leaf00219_log
#print axioms leaf00219_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
