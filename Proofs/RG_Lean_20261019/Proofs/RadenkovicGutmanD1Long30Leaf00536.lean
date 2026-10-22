/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00536 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 7870138074210584655349579513856000000000000 3125018916199457429878159095900691777978368 7324703026689251600800728219648000000000000))
theorem leaf00536_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 7870138074210584655349579513856000000000000 3125018916199457429878159095900691777978368 7324703026689251600800728219648000000000000 raw00536=true := by decide +kernel
#print axioms leaf00536_raw
theorem leaf00536_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00536=true := by decide +kernel
#print axioms leaf00536_rectangular
def affine00536 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00536 (IntegerComputedClassCell.leftNumerator ![(1/64),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/64),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/64),0,(1/16)] ![(1/3200),1,(1/16)]))
theorem leaf00536_transform : affine00536=(NestedInteger.clearedAll 3 raw00536 (IntegerComputedClassCell.leftNumerator ![(1/64),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/64),0,(1/16)] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/64),0,(1/16)] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00536_transform
theorem leaf00536_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00536=true := by decide +kernel
#print axioms leaf00536_sign
theorem leaf00536_log : RationalLog.accepts (1195406043/4294967296) (-2746541523/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00536_log
def leaf00536 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (426641039891/1000000000000) (1195406043/4294967296) (-2746541523/4294967296) 2 8 ![60,0,4] ![(1/64),0,(1/16)] ![(1/3200),1,(1/16)] affine00536
theorem leaf00536_checked : FastNestedCellData.accepts 1 2 4 leaf00536=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (426641039891/1000000000000) (1195406043/4294967296) (-2746541523/4294967296) 2 8 ![60,0,4] ![(1/64),0,(1/16)] ![(1/3200),1,(1/16)] 7870138074210584655349579513856000000000000 3125018916199457429878159095900691777978368 7324703026689251600800728219648000000000000 raw00536 affine00536
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00536_raw leaf00536_rectangular
    leaf00536_transform leaf00536_sign leaf00536_log
#print axioms leaf00536_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
