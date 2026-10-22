/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00515 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2226762697567623796319531827200000000000 16181703232968455454626028787033178112 20945466774293432460797542400000000000))
theorem leaf00515_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2226762697567623796319531827200000000000 16181703232968455454626028787033178112 20945466774293432460797542400000000000 raw00515=true := by decide +kernel
#print axioms leaf00515_raw
theorem leaf00515_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00515=true := by decide +kernel
#print axioms leaf00515_rectangular
def affine00515 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00515 (IntegerComputedClassCell.leftNumerator ![(23/1600),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/1600),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/1600),0,0] ![(1/3200),1,(1/16)]))
theorem leaf00515_transform : affine00515=(NestedInteger.clearedAll 3 raw00515 (IntegerComputedClassCell.leftNumerator ![(23/1600),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/1600),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/1600),0,0] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00515_transform
theorem leaf00515_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00515=true := by decide +kernel
#print axioms leaf00515_sign
theorem leaf00515_log : RationalLog.accepts (4401983/1073741824) (-11804395209/4294967296) 8 8=true := by decide +kernel
#print axioms leaf00515_log
def leaf00515 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (38628175269/50000000000) (4401983/1073741824) (-11804395209/4294967296) 8 8 ![60,0,4] ![(23/1600),0,0] ![(1/3200),1,(1/16)] affine00515
theorem leaf00515_checked : FastNestedCellData.accepts 1 2 4 leaf00515=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (38628175269/50000000000) (4401983/1073741824) (-11804395209/4294967296) 8 8 ![60,0,4] ![(23/1600),0,0] ![(1/3200),1,(1/16)] 2226762697567623796319531827200000000000 16181703232968455454626028787033178112 20945466774293432460797542400000000000 raw00515 affine00515
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00515_raw leaf00515_rectangular
    leaf00515_transform leaf00515_sign leaf00515_log
#print axioms leaf00515_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
