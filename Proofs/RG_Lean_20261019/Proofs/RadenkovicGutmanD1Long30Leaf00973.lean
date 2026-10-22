/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00973 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 528894007628145218451530579968000000000000 298023746214109658448451770338382417231872 649653769825498350637656571904000000000000))
theorem leaf00973_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 528894007628145218451530579968000000000000 298023746214109658448451770338382417231872 649653769825498350637656571904000000000000 raw00973=true := by decide +kernel
#print axioms leaf00973_raw
theorem leaf00973_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00973=true := by decide +kernel
#print axioms leaf00973_rectangular
def affine00973 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00973 (IntegerComputedClassCell.leftNumerator ![(9/80),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/80),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/80),0,(1/4)] ![(1/160),1,(1/4)]))
theorem leaf00973_transform : affine00973=(NestedInteger.clearedAll 3 raw00973 (IntegerComputedClassCell.leftNumerator ![(9/80),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(9/80),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(9/80),0,(1/4)] ![(1/160),1,(1/4)])) := by decide +kernel
#print axioms leaf00973_transform
theorem leaf00973_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00973=true := by decide +kernel
#print axioms leaf00973_sign
theorem leaf00973_log : RationalLog.accepts (1659065263/4294967296) (-2042664165/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00973_log
def leaf00973 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (114685606417/250000000000) (1659065263/4294967296) (-2042664165/4294967296) 2 8 ![60,0,4] ![(9/80),0,(1/4)] ![(1/160),1,(1/4)] affine00973
theorem leaf00973_checked : FastNestedCellData.accepts 1 2 4 leaf00973=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (114685606417/250000000000) (1659065263/4294967296) (-2042664165/4294967296) 2 8 ![60,0,4] ![(9/80),0,(1/4)] ![(1/160),1,(1/4)] 528894007628145218451530579968000000000000 298023746214109658448451770338382417231872 649653769825498350637656571904000000000000 raw00973 affine00973
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00973_raw leaf00973_rectangular
    leaf00973_transform leaf00973_sign leaf00973_log
#print axioms leaf00973_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
