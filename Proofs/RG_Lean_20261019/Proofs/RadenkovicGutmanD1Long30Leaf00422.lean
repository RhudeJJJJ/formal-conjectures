/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00422 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 149768458488466069342451557990400000000000 104795424055984989666492894619182708031488 645374328869617946272230014976000000000000))
theorem leaf00422_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 149768458488466069342451557990400000000000 104795424055984989666492894619182708031488 645374328869617946272230014976000000000000 raw00422=true := by decide +kernel
#print axioms leaf00422_raw
theorem leaf00422_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00422=true := by decide +kernel
#print axioms leaf00422_rectangular
def affine00422 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00422 (IntegerComputedClassCell.leftNumerator ![(17/1600),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(17/1600),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(17/1600),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00422_transform : affine00422=(NestedInteger.clearedAll 3 raw00422 (IntegerComputedClassCell.leftNumerator ![(17/1600),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(17/1600),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(17/1600),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00422_transform
theorem leaf00422_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00422=true := by decide +kernel
#print axioms leaf00422_sign
theorem leaf00422_log : RationalLog.accepts (1292718495/2147483648) (-1089954071/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00422_log
def leaf00422 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (162379288063/1000000000000) (1292718495/2147483648) (-1089954071/4294967296) 1 8 ![60,0,4] ![(17/1600),0,(1/8)] ![(1/6400),1,(1/8)] affine00422
theorem leaf00422_checked : FastNestedCellData.accepts 1 2 4 leaf00422=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (162379288063/1000000000000) (1292718495/2147483648) (-1089954071/4294967296) 1 8 ![60,0,4] ![(17/1600),0,(1/8)] ![(1/6400),1,(1/8)] 149768458488466069342451557990400000000000 104795424055984989666492894619182708031488 645374328869617946272230014976000000000000 raw00422 affine00422
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00422_raw leaf00422_rectangular
    leaf00422_transform leaf00422_sign leaf00422_log
#print axioms leaf00422_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
