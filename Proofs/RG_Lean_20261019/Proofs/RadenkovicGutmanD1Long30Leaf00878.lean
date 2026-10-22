/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00878 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 6722121235961128782912282427392000000000000 3584395226638732669751500501353058724216832 9836243513596337311039656820736000000000000))
theorem leaf00878_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 6722121235961128782912282427392000000000000 3584395226638732669751500501353058724216832 9836243513596337311039656820736000000000000 raw00878=true := by decide +kernel
#print axioms leaf00878_raw
theorem leaf00878_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00878=true := by decide +kernel
#print axioms leaf00878_rectangular
def affine00878 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00878 (IntegerComputedClassCell.leftNumerator ![(39/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(39/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(39/640),0,(1/4)] ![(1/640),1,(1/4)]))
theorem leaf00878_transform : affine00878=(NestedInteger.clearedAll 3 raw00878 (IntegerComputedClassCell.leftNumerator ![(39/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(39/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(39/640),0,(1/4)] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00878_transform
theorem leaf00878_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00878=true := by decide +kernel
#print axioms leaf00878_sign
theorem leaf00878_log : RationalLog.accepts (1678516043/4294967296) (-2017633641/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00878_log
def leaf00878 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (364406922387/1000000000000) (1678516043/4294967296) (-2017633641/4294967296) 2 8 ![60,0,4] ![(39/640),0,(1/4)] ![(1/640),1,(1/4)] affine00878
theorem leaf00878_checked : FastNestedCellData.accepts 1 2 4 leaf00878=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (364406922387/1000000000000) (1678516043/4294967296) (-2017633641/4294967296) 2 8 ![60,0,4] ![(39/640),0,(1/4)] ![(1/640),1,(1/4)] 6722121235961128782912282427392000000000000 3584395226638732669751500501353058724216832 9836243513596337311039656820736000000000000 raw00878 affine00878
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00878_raw leaf00878_rectangular
    leaf00878_transform leaf00878_sign leaf00878_log
#print axioms leaf00878_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
