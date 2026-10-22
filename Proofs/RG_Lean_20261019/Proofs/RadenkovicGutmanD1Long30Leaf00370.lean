/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00370 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4702083632163317182056743567360000000000 12158276900331977141035249773204996096 19079254211778656938795991040000000000))
theorem leaf00370_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4702083632163317182056743567360000000000 12158276900331977141035249773204996096 19079254211778656938795991040000000000 raw00370=true := by decide +kernel
#print axioms leaf00370_raw
theorem leaf00370_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00370=true := by decide +kernel
#print axioms leaf00370_rectangular
def affine00370 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00370 (IntegerComputedClassCell.leftNumerator ![(29/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(29/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(29/3200),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00370_transform : affine00370=(NestedInteger.clearedAll 3 raw00370 (IntegerComputedClassCell.leftNumerator ![(29/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(29/3200),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(29/3200),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00370_transform
theorem leaf00370_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00370=true := by decide +kernel
#print axioms leaf00370_sign
theorem leaf00370_log : RationalLog.accepts (6783069/4294967296) (-865807657/268435456) 10 8=true := by decide +kernel
#print axioms leaf00370_log
def leaf00370 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (12745023223/20000000000) (6783069/4294967296) (-865807657/268435456) 10 8 ![60,0,4] ![(29/3200),0,0] ![(1/6400),1,(1/16)] affine00370
theorem leaf00370_checked : FastNestedCellData.accepts 1 2 4 leaf00370=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (12745023223/20000000000) (6783069/4294967296) (-865807657/268435456) 10 8 ![60,0,4] ![(29/3200),0,0] ![(1/6400),1,(1/16)] 4702083632163317182056743567360000000000 12158276900331977141035249773204996096 19079254211778656938795991040000000000 raw00370 affine00370
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00370_raw leaf00370_rectangular
    leaf00370_transform leaf00370_sign leaf00370_log
#print axioms leaf00370_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
