/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00799 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 387387158667232237189716770816000000000000 288028239661823477212483821601807801516032 1959347793901446105332371685376000000000000))
theorem leaf00799_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 387387158667232237189716770816000000000000 288028239661823477212483821601807801516032 1959347793901446105332371685376000000000000 raw00799=true := by decide +kernel
#print axioms leaf00799_raw
theorem leaf00799_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00799=true := by decide +kernel
#print axioms leaf00799_rectangular
def affine00799 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00799 (IntegerComputedClassCell.leftNumerator ![(133/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(133/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(133/3200),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00799_transform : affine00799=(NestedInteger.clearedAll 3 raw00799 (IntegerComputedClassCell.leftNumerator ![(133/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(133/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(133/3200),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00799_transform
theorem leaf00799_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00799=true := by decide +kernel
#print axioms leaf00799_sign
theorem leaf00799_log : RationalLog.accepts (2784104281/4294967296) (-465486149/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00799_log
def leaf00799 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (147002099657/1000000000000) (2784104281/4294967296) (-465486149/2147483648) 1 8 ![60,0,4] ![(133/3200),0,(1/2)] ![(3/3200),1,(1/2)] affine00799
theorem leaf00799_checked : FastNestedCellData.accepts 1 2 4 leaf00799=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (147002099657/1000000000000) (2784104281/4294967296) (-465486149/2147483648) 1 8 ![60,0,4] ![(133/3200),0,(1/2)] ![(3/3200),1,(1/2)] 387387158667232237189716770816000000000000 288028239661823477212483821601807801516032 1959347793901446105332371685376000000000000 raw00799 affine00799
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00799_raw leaf00799_rectangular
    leaf00799_transform leaf00799_sign leaf00799_log
#print axioms leaf00799_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
