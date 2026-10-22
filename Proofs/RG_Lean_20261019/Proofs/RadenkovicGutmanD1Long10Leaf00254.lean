/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00254 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 29657703716167295543216701440000000000 21130195803065933890843839347180961792 122257991705806755309698416640000000000))
theorem leaf00254_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 29657703716167295543216701440000000000 21130195803065933890843839347180961792 122257991705806755309698416640000000000 raw00254=true := by decide +kernel
#print axioms leaf00254_raw
theorem leaf00254_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00254=true := by decide +kernel
#print axioms leaf00254_rectangular
def affine00254 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00254 (IntegerComputedClassCell.leftNumerator ![(1/20),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/20),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/20),0,(1/2)] ![(1/640),1,(1/2)]))
theorem leaf00254_transform : affine00254=(NestedInteger.clearedAll 3 raw00254 (IntegerComputedClassCell.leftNumerator ![(1/20),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(1/20),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(1/20),0,(1/2)] ![(1/640),1,(1/2)])) := by decide +kernel
#print axioms leaf00254_transform
theorem leaf00254_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00254=true := by decide +kernel
#print axioms leaf00254_sign
theorem leaf00254_log : RationalLog.accepts (2609094101/4294967296) (-66899603/268435456) 1 8=true := by decide +kernel
#print axioms leaf00254_log
def leaf00254 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (3456656781/20000000000) (2609094101/4294967296) (-66899603/268435456) 1 8 ![52,0,4] ![(1/20),0,(1/2)] ![(1/640),1,(1/2)] affine00254
theorem leaf00254_checked : FastNestedCellData.accepts 1 0 4 leaf00254=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (3456656781/20000000000) (2609094101/4294967296) (-66899603/268435456) 1 8 ![52,0,4] ![(1/20),0,(1/2)] ![(1/640),1,(1/2)] 29657703716167295543216701440000000000 21130195803065933890843839347180961792 122257991705806755309698416640000000000 raw00254 affine00254
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00254_raw leaf00254_rectangular
    leaf00254_transform leaf00254_sign leaf00254_log
#print axioms leaf00254_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
