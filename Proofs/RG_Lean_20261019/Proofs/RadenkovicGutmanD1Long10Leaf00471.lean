/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00471 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 26181503801016886189768048640000000000 26695938584969048200295452092319924224 47023000533802906233669156864000000000000))
theorem leaf00471_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 26181503801016886189768048640000000000 26695938584969048200295452092319924224 47023000533802906233669156864000000000000 raw00471=true := by decide +kernel
#print axioms leaf00471_raw
theorem leaf00471_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00471=true := by decide +kernel
#print axioms leaf00471_rectangular
def affine00471 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00471 (IntegerComputedClassCell.leftNumerator ![(13/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/128),0,0] ![(1/128),1,(1/2)]))
theorem leaf00471_transform : affine00471=(NestedInteger.clearedAll 3 raw00471 (IntegerComputedClassCell.leftNumerator ![(13/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(13/128),0,0] ![(1/128),1,(1/2)]) (IntegerComputedClassCell.denominator ![(13/128),0,0] ![(1/128),1,(1/2)])) := by decide +kernel
#print axioms leaf00471_transform
theorem leaf00471_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00471=true := by decide +kernel
#print axioms leaf00471_sign
theorem leaf00471_log : RationalLog.accepts (2188436675/2147483648) (40567429/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00471_log
def leaf00471 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (283860433/500000000000) (2188436675/2147483648) (40567429/4294967296) 0 8 ![52,0,4] ![(13/128),0,0] ![(1/128),1,(1/2)] affine00471
theorem leaf00471_checked : FastNestedCellData.accepts 1 0 4 leaf00471=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (283860433/500000000000) (2188436675/2147483648) (40567429/4294967296) 0 8 ![52,0,4] ![(13/128),0,0] ![(1/128),1,(1/2)] 26181503801016886189768048640000000000 26695938584969048200295452092319924224 47023000533802906233669156864000000000000 raw00471 affine00471
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00471_raw leaf00471_rectangular
    leaf00471_transform leaf00471_sign leaf00471_log
#print axioms leaf00471_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
