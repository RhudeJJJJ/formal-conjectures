/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00550 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 6769905423795056646442870374400000000 66634305574962843955548072689270784 83001690031655634522341376000000000))
theorem leaf00550_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 6769905423795056646442870374400000000 66634305574962843955548072689270784 83001690031655634522341376000000000 raw00550=true := by decide +kernel
#print axioms leaf00550_raw
theorem leaf00550_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00550=true := by decide +kernel
#print axioms leaf00550_rectangular
def affine00550 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00550 (IntegerComputedClassCell.leftNumerator ![(53/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(53/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(53/3200),0,0] ![(1/3200),1,(1/16)]))
theorem leaf00550_transform : affine00550=(NestedInteger.clearedAll 3 raw00550 (IntegerComputedClassCell.leftNumerator ![(53/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(53/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(53/3200),0,0] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00550_transform
theorem leaf00550_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00550=true := by decide +kernel
#print axioms leaf00550_sign
theorem leaf00550_log : RationalLog.accepts (11724545/2147483648) (-11189179357/4294967296) 8 8=true := by decide +kernel
#print axioms leaf00550_log
def leaf00550 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (6422452897/8000000000) (11724545/2147483648) (-11189179357/4294967296) 8 8 ![60,0,4] ![(53/3200),0,0] ![(1/3200),1,(1/16)] affine00550
theorem leaf00550_checked : FastNestedCellData.accepts 1 2 4 leaf00550=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (6422452897/8000000000) (11724545/2147483648) (-11189179357/4294967296) 8 8 ![60,0,4] ![(53/3200),0,0] ![(1/3200),1,(1/16)] 6769905423795056646442870374400000000 66634305574962843955548072689270784 83001690031655634522341376000000000 raw00550 affine00550
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00550_raw leaf00550_rectangular
    leaf00550_transform leaf00550_sign leaf00550_log
#print axioms leaf00550_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
