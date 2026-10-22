/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00472 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 26181503801016886189768048640000000000 26695938584969048200295452092319924224 47023000533802906233669156864000000000000))
theorem leaf00472_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 26181503801016886189768048640000000000 26695938584969048200295452092319924224 47023000533802906233669156864000000000000 raw00472=true := by decide +kernel
#print axioms leaf00472_raw
theorem leaf00472_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00472=true := by decide +kernel
#print axioms leaf00472_rectangular
def affine00472 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00472 (IntegerComputedClassCell.leftNumerator ![(13/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/128),0,(1/2)] ![(1/128),1,(1/4)]))
theorem leaf00472_transform : affine00472=(NestedInteger.clearedAll 3 raw00472 (IntegerComputedClassCell.leftNumerator ![(13/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/128),0,(1/2)] ![(1/128),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/128),0,(1/2)] ![(1/128),1,(1/4)])) := by decide +kernel
#print axioms leaf00472_transform
theorem leaf00472_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00472=true := by decide +kernel
#print axioms leaf00472_sign
theorem leaf00472_log : RationalLog.accepts (2188436675/2147483648) (40567429/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00472_log
def leaf00472 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (283860433/500000000000) (2188436675/2147483648) (40567429/4294967296) 0 8 ![52,0,4] ![(13/128),0,(1/2)] ![(1/128),1,(1/4)] affine00472
theorem leaf00472_checked : FastNestedCellData.accepts 1 0 4 leaf00472=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (283860433/500000000000) (2188436675/2147483648) (40567429/4294967296) 0 8 ![52,0,4] ![(13/128),0,(1/2)] ![(1/128),1,(1/4)] 26181503801016886189768048640000000000 26695938584969048200295452092319924224 47023000533802906233669156864000000000000 raw00472 affine00472
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00472_raw leaf00472_rectangular
    leaf00472_transform leaf00472_sign leaf00472_log
#print axioms leaf00472_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
