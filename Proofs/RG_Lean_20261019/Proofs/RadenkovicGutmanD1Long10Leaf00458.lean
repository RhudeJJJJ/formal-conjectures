/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00458 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 48826415297288814946661957632000000000000 51408240523757455603753955266277779963904 19422164220892848165460536983552000000000000))
theorem leaf00458_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 48826415297288814946661957632000000000000 51408240523757455603753955266277779963904 19422164220892848165460536983552000000000000 raw00458=true := by decide +kernel
#print axioms leaf00458_raw
theorem leaf00458_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00458=true := by decide +kernel
#print axioms leaf00458_rectangular
def affine00458 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00458 (IntegerComputedClassCell.leftNumerator ![(11/64),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/64),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/64),0,(3/4)] ![(1/64),1,(1/4)]))
theorem leaf00458_transform : affine00458=(NestedInteger.clearedAll 3 raw00458 (IntegerComputedClassCell.leftNumerator ![(11/64),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/64),0,(3/4)] ![(1/64),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/64),0,(3/4)] ![(1/64),1,(1/4)])) := by decide +kernel
#print axioms leaf00458_transform
theorem leaf00458_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00458=true := by decide +kernel
#print axioms leaf00458_sign
theorem leaf00458_log : RationalLog.accepts (4510137181/4294967296) (52488397/2147483648) 0 8=true := by decide +kernel
#print axioms leaf00458_log
def leaf00458 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (2646885277/1000000000000) (4510137181/4294967296) (52488397/2147483648) 0 8 ![52,0,4] ![(11/64),0,(3/4)] ![(1/64),1,(1/4)] affine00458
theorem leaf00458_checked : FastNestedCellData.accepts 1 0 4 leaf00458=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (2646885277/1000000000000) (4510137181/4294967296) (52488397/2147483648) 0 8 ![52,0,4] ![(11/64),0,(3/4)] ![(1/64),1,(1/4)] 48826415297288814946661957632000000000000 51408240523757455603753955266277779963904 19422164220892848165460536983552000000000000 raw00458 affine00458
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00458_raw leaf00458_rectangular
    leaf00458_transform leaf00458_sign leaf00458_log
#print axioms leaf00458_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
