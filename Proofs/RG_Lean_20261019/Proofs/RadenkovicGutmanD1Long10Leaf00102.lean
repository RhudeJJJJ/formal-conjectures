/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00102 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 286543525275175198544774561792000000000000 436412995836804380495014262546406309888 1755928448590706044582232064000000000000))
theorem leaf00102_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 286543525275175198544774561792000000000000 436412995836804380495014262546406309888 1755928448590706044582232064000000000000 raw00102=true := by decide +kernel
#print axioms leaf00102_raw
theorem leaf00102_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00102=true := by decide +kernel
#print axioms leaf00102_rectangular
def affine00102 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00102 (IntegerComputedClassCell.leftNumerator ![(7/640),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/640),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/640),0,0] ![(1/3200),1,(1/4)]))
theorem leaf00102_transform : affine00102=(NestedInteger.clearedAll 3 raw00102 (IntegerComputedClassCell.leftNumerator ![(7/640),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/640),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/640),0,0] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00102_transform
theorem leaf00102_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00102=true := by decide +kernel
#print axioms leaf00102_sign
theorem leaf00102_log : RationalLog.accepts (5239207/4294967296) (-3601882643/1073741824) 10 8=true := by decide +kernel
#print axioms leaf00102_log
def leaf00102 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (62134222523/250000000000) (5239207/4294967296) (-3601882643/1073741824) 10 8 ![52,0,4] ![(7/640),0,0] ![(1/3200),1,(1/4)] affine00102
theorem leaf00102_checked : FastNestedCellData.accepts 1 0 4 leaf00102=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (62134222523/250000000000) (5239207/4294967296) (-3601882643/1073741824) 10 8 ![52,0,4] ![(7/640),0,0] ![(1/3200),1,(1/4)] 286543525275175198544774561792000000000000 436412995836804380495014262546406309888 1755928448590706044582232064000000000000 raw00102 affine00102
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00102_raw leaf00102_rectangular
    leaf00102_transform leaf00102_sign leaf00102_log
#print axioms leaf00102_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
