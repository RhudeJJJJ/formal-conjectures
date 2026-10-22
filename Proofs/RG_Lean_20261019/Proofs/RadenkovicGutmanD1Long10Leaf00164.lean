/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00164 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 89346414440910121720610816000000000000 74861805828596003502568527467510759424 943371938716472833512308736000000000000))
theorem leaf00164_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 89346414440910121720610816000000000000 74861805828596003502568527467510759424 943371938716472833512308736000000000000 raw00164=true := by decide +kernel
#print axioms leaf00164_raw
theorem leaf00164_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00164=true := by decide +kernel
#print axioms leaf00164_rectangular
def affine00164 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00164 (IntegerComputedClassCell.leftNumerator ![(7/320),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/320),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/320),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00164_transform : affine00164=(NestedInteger.clearedAll 3 raw00164 (IntegerComputedClassCell.leftNumerator ![(7/320),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/320),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/320),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00164_transform
theorem leaf00164_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00164=true := by decide +kernel
#print axioms leaf00164_sign
theorem leaf00164_log : RationalLog.accepts (1667049533/2147483648) (-271915947/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00164_log
def leaf00164 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (1239930581/15625000000) (1667049533/2147483648) (-271915947/2147483648) 1 8 ![52,0,4] ![(7/320),0,(1/2)] ![(3/6400),1,(1/2)] affine00164
theorem leaf00164_checked : FastNestedCellData.accepts 1 0 4 leaf00164=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (1239930581/15625000000) (1667049533/2147483648) (-271915947/2147483648) 1 8 ![52,0,4] ![(7/320),0,(1/2)] ![(3/6400),1,(1/2)] 89346414440910121720610816000000000000 74861805828596003502568527467510759424 943371938716472833512308736000000000000 raw00164 affine00164
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00164_raw leaf00164_rectangular
    leaf00164_transform leaf00164_sign leaf00164_log
#print axioms leaf00164_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
