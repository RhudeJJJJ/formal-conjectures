/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00094 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 7340050473364457481775874048000000000000 6160476408218117668193646473858141650944 80636885666198788658423660544000000000000))
theorem leaf00094_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 7340050473364457481775874048000000000000 6160476408218117668193646473858141650944 80636885666198788658423660544000000000000 raw00094=true := by decide +kernel
#print axioms leaf00094_raw
theorem leaf00094_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00094=true := by decide +kernel
#print axioms leaf00094_rectangular
def affine00094 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00094 (IntegerComputedClassCell.leftNumerator ![(1/100),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/100),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/100),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00094_transform : affine00094=(NestedInteger.clearedAll 3 raw00094 (IntegerComputedClassCell.leftNumerator ![(1/100),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/100),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/100),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00094_transform
theorem leaf00094_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00094=true := by decide +kernel
#print axioms leaf00094_sign
theorem leaf00094_log : RationalLog.accepts (837225297/1073741824) (-534318991/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00094_log
def leaf00094 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (38198873613/500000000000) (837225297/1073741824) (-534318991/4294967296) 1 8 ![52,0,4] ![(1/100),0,(1/4)] ![(1/3200),1,(1/4)] affine00094
theorem leaf00094_checked : FastNestedCellData.accepts 1 0 4 leaf00094=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (38198873613/500000000000) (837225297/1073741824) (-534318991/4294967296) 1 8 ![52,0,4] ![(1/100),0,(1/4)] ![(1/3200),1,(1/4)] 7340050473364457481775874048000000000000 6160476408218117668193646473858141650944 80636885666198788658423660544000000000000 raw00094 affine00094
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00094_raw leaf00094_rectangular
    leaf00094_transform leaf00094_sign leaf00094_log
#print axioms leaf00094_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
