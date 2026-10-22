/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00018 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1370162380503679796128702791680000000000 1339717132716094777401091935321607634944 144294833546914199412274521702400000000000))
theorem leaf00018_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1370162380503679796128702791680000000000 1339717132716094777401091935321607634944 144294833546914199412274521702400000000000 raw00018=true := by decide +kernel
#print axioms leaf00018_raw
theorem leaf00018_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00018=true := by decide +kernel
#print axioms leaf00018_rectangular
def affine00018 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00018 (IntegerComputedClassCell.leftNumerator ![(19/16000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/16000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/16000),0,(1/4)] ![(1/16000),1,(1/4)]))
theorem leaf00018_transform : affine00018=(NestedInteger.clearedAll 3 raw00018 (IntegerComputedClassCell.leftNumerator ![(19/16000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/16000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/16000),0,(1/4)] ![(1/16000),1,(1/4)])) := by decide +kernel
#print axioms leaf00018_transform
theorem leaf00018_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00018=true := by decide +kernel
#print axioms leaf00018_sign
theorem leaf00018_log : RationalLog.accepts (4160900155/4294967296) (-34051063/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00018_log
def leaf00018 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (1856916287/200000000000) (4160900155/4294967296) (-34051063/2147483648) 1 8 ![60,0,4] ![(19/16000),0,(1/4)] ![(1/16000),1,(1/4)] affine00018
theorem leaf00018_checked : FastNestedCellData.accepts 1 2 4 leaf00018=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (1856916287/200000000000) (4160900155/4294967296) (-34051063/2147483648) 1 8 ![60,0,4] ![(19/16000),0,(1/4)] ![(1/16000),1,(1/4)] 1370162380503679796128702791680000000000 1339717132716094777401091935321607634944 144294833546914199412274521702400000000000 raw00018 affine00018
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00018_raw leaf00018_rectangular
    leaf00018_transform leaf00018_sign leaf00018_log
#print axioms leaf00018_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
