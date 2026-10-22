/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00486 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1667036679876385914735975989248000000000000 760924748006298374654490123710093057851392 2105020281687047090088827682816000000000000))
theorem leaf00486_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1667036679876385914735975989248000000000000 760924748006298374654490123710093057851392 2105020281687047090088827682816000000000000 raw00486=true := by decide +kernel
#print axioms leaf00486_raw
theorem leaf00486_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00486=true := by decide +kernel
#print axioms leaf00486_rectangular
def affine00486 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00486 (IntegerComputedClassCell.leftNumerator ![(81/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(81/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(81/6400),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00486_transform : affine00486=(NestedInteger.clearedAll 3 raw00486 (IntegerComputedClassCell.leftNumerator ![(81/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(81/6400),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(81/6400),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00486_transform
theorem leaf00486_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00486=true := by decide +kernel
#print axioms leaf00486_sign
theorem leaf00486_log : RationalLog.accepts (719970741/2147483648) (-146678703/268435456) 2 8=true := by decide +kernel
#print axioms leaf00486_log
def leaf00486 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (361480957987/1000000000000) (719970741/2147483648) (-146678703/268435456) 2 8 ![60,0,4] ![(81/6400),0,(1/16)] ![(1/6400),1,(1/16)] affine00486
theorem leaf00486_checked : FastNestedCellData.accepts 1 2 4 leaf00486=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (361480957987/1000000000000) (719970741/2147483648) (-146678703/268435456) 2 8 ![60,0,4] ![(81/6400),0,(1/16)] ![(1/6400),1,(1/16)] 1667036679876385914735975989248000000000000 760924748006298374654490123710093057851392 2105020281687047090088827682816000000000000 raw00486 affine00486
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00486_raw leaf00486_rectangular
    leaf00486_transform leaf00486_sign leaf00486_log
#print axioms leaf00486_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
