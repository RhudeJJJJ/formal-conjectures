/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00491 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 328597616792511277170688000000000000 329085342503226698768061867755569152 26241653291670164548161110016000000000000))
theorem leaf00491_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 328597616792511277170688000000000000 329085342503226698768061867755569152 26241653291670164548161110016000000000000 raw00491=true := by decide +kernel
#print axioms leaf00491_raw
theorem leaf00491_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00491=true := by decide +kernel
#print axioms leaf00491_rectangular
def affine00491 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00491 (IntegerComputedClassCell.leftNumerator ![(7/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(7/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(7/256),0,0] ![(1/256),1,1]))
theorem leaf00491_transform : affine00491=(NestedInteger.clearedAll 3 raw00491 (IntegerComputedClassCell.leftNumerator ![(7/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(7/256),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(7/256),0,0] ![(1/256),1,1])) := by decide +kernel
#print axioms leaf00491_transform
theorem leaf00491_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00491=true := by decide +kernel
#print axioms leaf00491_sign
theorem leaf00491_log : RationalLog.accepts (2150644111/2147483648) (3158139/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00491_log
def leaf00491 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (3135143/250000000000) (2150644111/2147483648) (3158139/4294967296) 0 8 ![52,0,4] ![(7/256),0,0] ![(1/256),1,1] affine00491
theorem leaf00491_checked : FastNestedCellData.accepts 1 0 4 leaf00491=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (3135143/250000000000) (2150644111/2147483648) (3158139/4294967296) 0 8 ![52,0,4] ![(7/256),0,0] ![(1/256),1,1] 328597616792511277170688000000000000 329085342503226698768061867755569152 26241653291670164548161110016000000000000 raw00491 affine00491
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00491_raw leaf00491_rectangular
    leaf00491_transform leaf00491_sign leaf00491_log
#print axioms leaf00491_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
