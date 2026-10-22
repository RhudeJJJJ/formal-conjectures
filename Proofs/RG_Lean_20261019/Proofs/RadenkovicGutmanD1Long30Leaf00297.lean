/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00297 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3090228621401138737262194851840000000000 2439399458216348396111811205909041905664 23298717609500234787585796341760000000000))
theorem leaf00297_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3090228621401138737262194851840000000000 2439399458216348396111811205909041905664 23298717609500234787585796341760000000000 raw00297=true := by decide +kernel
#print axioms leaf00297_raw
theorem leaf00297_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00297=true := by decide +kernel
#print axioms leaf00297_rectangular
def affine00297 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00297 (IntegerComputedClassCell.leftNumerator ![(43/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(43/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(43/6400),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00297_transform : affine00297=(NestedInteger.clearedAll 3 raw00297 (IntegerComputedClassCell.leftNumerator ![(43/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(43/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(43/6400),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00297_transform
theorem leaf00297_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00297=true := by decide +kernel
#print axioms leaf00297_sign
theorem leaf00297_log : RationalLog.accepts (3069074419/4294967296) (-90212549/536870912) 1 8=true := by decide +kernel
#print axioms leaf00297_log
def leaf00297 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (4188040731/40000000000) (3069074419/4294967296) (-90212549/536870912) 1 8 ![60,0,4] ![(43/6400),0,(1/8)] ![(1/6400),1,(1/8)] affine00297
theorem leaf00297_checked : FastNestedCellData.accepts 1 2 4 leaf00297=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (4188040731/40000000000) (3069074419/4294967296) (-90212549/536870912) 1 8 ![60,0,4] ![(43/6400),0,(1/8)] ![(1/6400),1,(1/8)] 3090228621401138737262194851840000000000 2439399458216348396111811205909041905664 23298717609500234787585796341760000000000 raw00297 affine00297
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00297_raw leaf00297_rectangular
    leaf00297_transform leaf00297_sign leaf00297_log
#print axioms leaf00297_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
