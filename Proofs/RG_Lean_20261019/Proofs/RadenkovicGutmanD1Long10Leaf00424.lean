/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00424 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack true 913422752261862470843283537920000000000 1105455040602740602483434716900330831872 44649744422273621597776720691200000000000))
theorem leaf00424_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    true 913422752261862470843283537920000000000 1105455040602740602483434716900330831872 44649744422273621597776720691200000000000 raw00424=true := by decide +kernel
#print axioms leaf00424_raw
theorem leaf00424_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00424=true := by decide +kernel
#print axioms leaf00424_rectangular
def affine00424 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00424 (IntegerComputedClassCell.leftNumerator ![(13/32),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/32),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/32),0,(1/2)] ![(1/32),1,(1/4)]))
theorem leaf00424_transform : affine00424=(NestedInteger.clearedAll 3 raw00424 (IntegerComputedClassCell.leftNumerator ![(13/32),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/32),0,(1/2)] ![(1/32),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/32),0,(1/2)] ![(1/32),1,(1/4)])) := by decide +kernel
#print axioms leaf00424_transform
theorem leaf00424_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00424=true := by decide +kernel
#print axioms leaf00424_sign
theorem leaf00424_log : RationalLog.accepts (5072331685/4294967296) (357248227/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00424_log
def leaf00424 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack true (2475837331/100000000000) (5072331685/4294967296) (357248227/4294967296) 0 8 ![52,0,4] ![(13/32),0,(1/2)] ![(1/32),1,(1/4)] affine00424
theorem leaf00424_checked : FastNestedCellData.accepts 1 0 4 leaf00424=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack true (2475837331/100000000000) (5072331685/4294967296) (357248227/4294967296) 0 8 ![52,0,4] ![(13/32),0,(1/2)] ![(1/32),1,(1/4)] 913422752261862470843283537920000000000 1105455040602740602483434716900330831872 44649744422273621597776720691200000000000 raw00424 affine00424
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00424_raw leaf00424_rectangular
    leaf00424_transform leaf00424_sign leaf00424_log
#print axioms leaf00424_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
