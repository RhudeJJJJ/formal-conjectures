/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00158 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 484850262580550380678876758016000000000000 455895942153382825452183695748224727908352 17345140176651940145407356567552000000000000))
theorem leaf00158_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 484850262580550380678876758016000000000000 455895942153382825452183695748224727908352 17345140176651940145407356567552000000000000 raw00158=true := by decide +kernel
#print axioms leaf00158_raw
theorem leaf00158_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00158=true := by decide +kernel
#print axioms leaf00158_rectangular
def affine00158 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00158 (IntegerComputedClassCell.leftNumerator ![(109/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(109/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(109/32000),0,(1/4)] ![(3/32000),1,(1/4)]))
theorem leaf00158_transform : affine00158=(NestedInteger.clearedAll 3 raw00158 (IntegerComputedClassCell.leftNumerator ![(109/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(109/32000),0,(1/4)] ![(3/32000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(109/32000),0,(1/4)] ![(3/32000),1,(1/4)])) := by decide +kernel
#print axioms leaf00158_transform
theorem leaf00158_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00158=true := by decide +kernel
#print axioms leaf00158_sign
theorem leaf00158_log : RationalLog.accepts (3935052087/4294967296) (-187947423/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00158_log
def leaf00158 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (26283785401/1000000000000) (3935052087/4294967296) (-187947423/4294967296) 1 8 ![60,0,4] ![(109/32000),0,(1/4)] ![(3/32000),1,(1/4)] affine00158
theorem leaf00158_checked : FastNestedCellData.accepts 1 2 4 leaf00158=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (26283785401/1000000000000) (3935052087/4294967296) (-187947423/4294967296) 1 8 ![60,0,4] ![(109/32000),0,(1/4)] ![(3/32000),1,(1/4)] 484850262580550380678876758016000000000000 455895942153382825452183695748224727908352 17345140176651940145407356567552000000000000 raw00158 affine00158
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00158_raw leaf00158_rectangular
    leaf00158_transform leaf00158_sign leaf00158_log
#print axioms leaf00158_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
