/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00309 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 12748173884340553648747577344000000000000 2513442207828546421179977495276240764928 3551736113200800847634628608000000000000))
theorem leaf00309_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 12748173884340553648747577344000000000000 2513442207828546421179977495276240764928 3551736113200800847634628608000000000000 raw00309=true := by decide +kernel
#print axioms leaf00309_raw
theorem leaf00309_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00309=true := by decide +kernel
#print axioms leaf00309_rectangular
def affine00309 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00309 (IntegerComputedClassCell.leftNumerator ![(29/320),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(29/320),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(29/320),0,0] ![(1/320),1,(1/4)]))
theorem leaf00309_transform : affine00309=(NestedInteger.clearedAll 3 raw00309 (IntegerComputedClassCell.leftNumerator ![(29/320),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(29/320),0,0] ![(1/320),1,(1/4)]) (IntegerComputedClassCell.denominator ![(29/320),0,0] ![(1/320),1,(1/4)])) := by decide +kernel
#print axioms leaf00309_transform
theorem leaf00309_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00309=true := by decide +kernel
#print axioms leaf00309_sign
theorem leaf00309_log : RationalLog.accepts (495881497/4294967296) (-4636121499/4294967296) 4 8=true := by decide +kernel
#print axioms leaf00309_log
def leaf00309 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (22114556513/31250000000) (495881497/4294967296) (-4636121499/4294967296) 4 8 ![52,0,4] ![(29/320),0,0] ![(1/320),1,(1/4)] affine00309
theorem leaf00309_checked : FastNestedCellData.accepts 1 0 4 leaf00309=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (22114556513/31250000000) (495881497/4294967296) (-4636121499/4294967296) 4 8 ![52,0,4] ![(29/320),0,0] ![(1/320),1,(1/4)] 12748173884340553648747577344000000000000 2513442207828546421179977495276240764928 3551736113200800847634628608000000000000 raw00309 affine00309
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00309_raw leaf00309_rectangular
    leaf00309_transform leaf00309_sign leaf00309_log
#print axioms leaf00309_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
