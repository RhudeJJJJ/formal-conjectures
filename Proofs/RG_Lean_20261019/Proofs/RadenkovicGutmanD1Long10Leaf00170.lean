/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00170 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 96204816905487747740382265344000000000000 79707740054340377685482121838562446934016 955220024819979096619130814464000000000000))
theorem leaf00170_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 96204816905487747740382265344000000000000 79707740054340377685482121838562446934016 955220024819979096619130814464000000000000 raw00170=true := by decide +kernel
#print axioms leaf00170_raw
theorem leaf00170_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00170=true := by decide +kernel
#print axioms leaf00170_rectangular
def affine00170 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00170 (IntegerComputedClassCell.leftNumerator ![(73/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(73/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(73/3200),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00170_transform : affine00170=(NestedInteger.clearedAll 3 raw00170 (IntegerComputedClassCell.leftNumerator ![(73/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(73/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(73/3200),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00170_transform
theorem leaf00170_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00170=true := by decide +kernel
#print axioms leaf00170_sign
theorem leaf00170_log : RationalLog.accepts (1642203313/2147483648) (-36004973/268435456) 1 8=true := by decide +kernel
#print axioms leaf00170_log
def leaf00170 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (41722188597/500000000000) (1642203313/2147483648) (-36004973/268435456) 1 8 ![52,0,4] ![(73/3200),0,(1/2)] ![(3/3200),1,(1/2)] affine00170
theorem leaf00170_checked : FastNestedCellData.accepts 1 0 4 leaf00170=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (41722188597/500000000000) (1642203313/2147483648) (-36004973/268435456) 1 8 ![52,0,4] ![(73/3200),0,(1/2)] ![(3/3200),1,(1/2)] 96204816905487747740382265344000000000000 79707740054340377685482121838562446934016 955220024819979096619130814464000000000000 raw00170 affine00170
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00170_raw leaf00170_rectangular
    leaf00170_transform leaf00170_sign leaf00170_log
#print axioms leaf00170_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
