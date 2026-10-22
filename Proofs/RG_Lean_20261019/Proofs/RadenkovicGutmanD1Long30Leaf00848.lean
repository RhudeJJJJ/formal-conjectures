/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00848 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 242670246071212002267365795430400000000000 133152385595242920970099145227108167450624 404866772032456271144973395558400000000000))
theorem leaf00848_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 242670246071212002267365795430400000000000 133152385595242920970099145227108167450624 404866772032456271144973395558400000000000 raw00848=true := by decide +kernel
#print axioms leaf00848_raw
theorem leaf00848_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00848=true := by decide +kernel
#print axioms leaf00848_rectangular
def affine00848 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00848 (IntegerComputedClassCell.leftNumerator ![(33/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(33/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(33/640),0,(1/4)] ![(1/640),1,(1/4)]))
theorem leaf00848_transform : affine00848=(NestedInteger.clearedAll 3 raw00848 (IntegerComputedClassCell.leftNumerator ![(33/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(33/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(33/640),0,(1/4)] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00848_transform
theorem leaf00848_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00848=true := by decide +kernel
#print axioms leaf00848_sign
theorem leaf00848_log : RationalLog.accepts (1773399891/4294967296) (-949773421/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00848_log
def leaf00848 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (65775901997/200000000000) (1773399891/4294967296) (-949773421/2147483648) 2 8 ![60,0,4] ![(33/640),0,(1/4)] ![(1/640),1,(1/4)] affine00848
theorem leaf00848_checked : FastNestedCellData.accepts 1 2 4 leaf00848=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (65775901997/200000000000) (1773399891/4294967296) (-949773421/2147483648) 2 8 ![60,0,4] ![(33/640),0,(1/4)] ![(1/640),1,(1/4)] 242670246071212002267365795430400000000000 133152385595242920970099145227108167450624 404866772032456271144973395558400000000000 raw00848 affine00848
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00848_raw leaf00848_rectangular
    leaf00848_transform leaf00848_sign leaf00848_log
#print axioms leaf00848_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
