/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01099 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 83310026540467595297645658112000000000000 94607702730120770370670557660639506989056 436423079383788878122237034496000000000000))
theorem leaf01099_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 83310026540467595297645658112000000000000 94607702730120770370670557660639506989056 436423079383788878122237034496000000000000 raw01099=true := by decide +kernel
#print axioms leaf01099_raw
theorem leaf01099_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01099=true := by decide +kernel
#print axioms leaf01099_rectangular
def affine01099 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01099 (IntegerComputedClassCell.leftNumerator ![(1/2),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/2),0,(15/16)] ![(1/32),1,(1/16)]))
theorem leaf01099_transform : affine01099=(NestedInteger.clearedAll 3 raw01099 (IntegerComputedClassCell.leftNumerator ![(1/2),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/2),0,(15/16)] ![(1/32),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/2),0,(15/16)] ![(1/32),1,(1/16)])) := by decide +kernel
#print axioms leaf01099_transform
theorem leaf01099_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01099=true := by decide +kernel
#print axioms leaf01099_sign
theorem leaf01099_log : RationalLog.accepts (4008455793/4294967296) (-74128859/2147483648) 1 8=true := by decide +kernel
#print axioms leaf01099_log
def leaf01099 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (54194947059/250000000000) (4008455793/4294967296) (-74128859/2147483648) 1 8 ![60,0,4] ![(1/2),0,(15/16)] ![(1/32),1,(1/16)] affine01099
theorem leaf01099_checked : FastNestedCellData.accepts 1 2 4 leaf01099=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (54194947059/250000000000) (4008455793/4294967296) (-74128859/2147483648) 1 8 ![60,0,4] ![(1/2),0,(15/16)] ![(1/32),1,(1/16)] 83310026540467595297645658112000000000000 94607702730120770370670557660639506989056 436423079383788878122237034496000000000000 raw01099 affine01099
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01099_raw leaf01099_rectangular
    leaf01099_transform leaf01099_sign leaf01099_log
#print axioms leaf01099_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
