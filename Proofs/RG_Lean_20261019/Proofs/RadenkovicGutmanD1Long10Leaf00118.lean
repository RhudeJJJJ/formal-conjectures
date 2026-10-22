/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00118 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 23177885598486915566718785945600000000000 18414522241978198908178689124897325580288 183196164288805623232248938496000000000000))
theorem leaf00118_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 23177885598486915566718785945600000000000 18414522241978198908178689124897325580288 183196164288805623232248938496000000000000 raw00118=true := by decide +kernel
#print axioms leaf00118_raw
theorem leaf00118_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00118=true := by decide +kernel
#print axioms leaf00118_rectangular
def affine00118 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00118 (IntegerComputedClassCell.leftNumerator ![(21/1600),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(21/1600),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(21/1600),0,(1/4)] ![(1/1600),1,(1/4)]))
theorem leaf00118_transform : affine00118=(NestedInteger.clearedAll 3 raw00118 (IntegerComputedClassCell.leftNumerator ![(21/1600),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(21/1600),0,(1/4)] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(21/1600),0,(1/4)] ![(1/1600),1,(1/4)])) := by decide +kernel
#print axioms leaf00118_transform
theorem leaf00118_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00118=true := by decide +kernel
#print axioms leaf00118_sign
theorem leaf00118_log : RationalLog.accepts (1550312805/2147483648) (-349868097/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00118_log
def leaf00118 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (50259027839/500000000000) (1550312805/2147483648) (-349868097/2147483648) 1 8 ![52,0,4] ![(21/1600),0,(1/4)] ![(1/1600),1,(1/4)] affine00118
theorem leaf00118_checked : FastNestedCellData.accepts 1 0 4 leaf00118=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (50259027839/500000000000) (1550312805/2147483648) (-349868097/2147483648) 1 8 ![52,0,4] ![(21/1600),0,(1/4)] ![(1/1600),1,(1/4)] 23177885598486915566718785945600000000000 18414522241978198908178689124897325580288 183196164288805623232248938496000000000000 raw00118 affine00118
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00118_raw leaf00118_rectangular
    leaf00118_transform leaf00118_sign leaf00118_log
#print axioms leaf00118_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
