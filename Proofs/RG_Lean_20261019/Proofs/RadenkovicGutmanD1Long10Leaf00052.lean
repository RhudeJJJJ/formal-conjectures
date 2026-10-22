/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00052 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 806285817760328800005424939008000000000000 726321340385791934398761849391148420825088 16617263489251977468345661259776000000000000))
theorem leaf00052_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 806285817760328800005424939008000000000000 726321340385791934398761849391148420825088 16617263489251977468345661259776000000000000 raw00052=true := by decide +kernel
#print axioms leaf00052_raw
theorem leaf00052_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00052=true := by decide +kernel
#print axioms leaf00052_rectangular
def affine00052 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00052 (IntegerComputedClassCell.leftNumerator ![(9/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/1600),0,(1/4)] ![(1/3200),1,(1/4)]))
theorem leaf00052_transform : affine00052=(NestedInteger.clearedAll 3 raw00052 (IntegerComputedClassCell.leftNumerator ![(9/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/1600),0,(1/4)] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/1600),0,(1/4)] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00052_transform
theorem leaf00052_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00052=true := by decide +kernel
#print axioms leaf00052_sign
theorem leaf00052_log : RationalLog.accepts (3706980337/4294967296) (-316166153/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00052_log
def leaf00052 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (43708841763/1000000000000) (3706980337/4294967296) (-316166153/4294967296) 1 8 ![52,0,4] ![(9/1600),0,(1/4)] ![(1/3200),1,(1/4)] affine00052
theorem leaf00052_checked : FastNestedCellData.accepts 1 0 4 leaf00052=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (43708841763/1000000000000) (3706980337/4294967296) (-316166153/4294967296) 1 8 ![52,0,4] ![(9/1600),0,(1/4)] ![(1/3200),1,(1/4)] 806285817760328800005424939008000000000000 726321340385791934398761849391148420825088 16617263489251977468345661259776000000000000 raw00052 affine00052
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00052_raw leaf00052_rectangular
    leaf00052_transform leaf00052_sign leaf00052_log
#print axioms leaf00052_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
