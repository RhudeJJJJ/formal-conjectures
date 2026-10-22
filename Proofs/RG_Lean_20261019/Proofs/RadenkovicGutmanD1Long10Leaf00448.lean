/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00448 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 485026879299147262257528832000000000000 524347828464802970464419695557028610048 103865701938778507248844931072000000000000))
theorem leaf00448_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 485026879299147262257528832000000000000 524347828464802970464419695557028610048 103865701938778507248844931072000000000000 raw00448=true := by decide +kernel
#print axioms leaf00448_raw
theorem leaf00448_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00448=true := by decide +kernel
#print axioms leaf00448_rectangular
def affine00448 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00448 (IntegerComputedClassCell.leftNumerator ![(7/32),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/32),0,(1/2)] ![(1/64),1,(1/4)]))
theorem leaf00448_transform : affine00448=(NestedInteger.clearedAll 3 raw00448 (IntegerComputedClassCell.leftNumerator ![(7/32),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/32),0,(1/2)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/32),0,(1/2)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf00448_transform
theorem leaf00448_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00448=true := by decide +kernel
#print axioms leaf00448_sign
theorem leaf00448_log : RationalLog.accepts (2309918133/2147483648) (9786529/268435456) 0 8=true := by decide +kernel
#print axioms leaf00448_log
def leaf00448 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (1262081271/250000000000) (2309918133/2147483648) (9786529/268435456) 0 8 ![52,0,4] ![(7/32),0,(1/2)] ![(1/64),1,(1/4)] affine00448
theorem leaf00448_checked : FastNestedCellData.accepts 1 0 4 leaf00448=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (1262081271/250000000000) (2309918133/2147483648) (9786529/268435456) 0 8 ![52,0,4] ![(7/32),0,(1/2)] ![(1/64),1,(1/4)] 485026879299147262257528832000000000000 524347828464802970464419695557028610048 103865701938778507248844931072000000000000 raw00448 affine00448
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00448_raw leaf00448_rectangular
    leaf00448_transform leaf00448_sign leaf00448_log
#print axioms leaf00448_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
