/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00315 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 8647315259023194522325614592000000000000 13616994878720060958752540055146856448 24126438515107837851467776000000000000))
theorem leaf00315_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 8647315259023194522325614592000000000000 13616994878720060958752540055146856448 24126438515107837851467776000000000000 raw00315=true := by decide +kernel
#print axioms leaf00315_raw
theorem leaf00315_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00315=true := by decide +kernel
#print axioms leaf00315_rectangular
def affine00315 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00315 (IntegerComputedClassCell.leftNumerator ![(47/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(47/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(47/6400),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00315_transform : affine00315=(NestedInteger.clearedAll 3 raw00315 (IntegerComputedClassCell.leftNumerator ![(47/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(47/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(47/6400),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00315_transform
theorem leaf00315_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00315=true := by decide +kernel
#print axioms leaf00315_sign
theorem leaf00315_log : RationalLog.accepts (4323263/4294967296) (-14820190407/4294967296) 10 8=true := by decide +kernel
#print axioms leaf00315_log
def leaf00315 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (282200683499/500000000000) (4323263/4294967296) (-14820190407/4294967296) 10 8 ![60,0,4] ![(47/6400),0,0] ![(1/6400),1,(1/16)] affine00315
theorem leaf00315_checked : FastNestedCellData.accepts 1 2 4 leaf00315=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (282200683499/500000000000) (4323263/4294967296) (-14820190407/4294967296) 10 8 ![60,0,4] ![(47/6400),0,0] ![(1/6400),1,(1/16)] 8647315259023194522325614592000000000000 13616994878720060958752540055146856448 24126438515107837851467776000000000000 raw00315 affine00315
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00315_raw leaf00315_rectangular
    leaf00315_transform leaf00315_sign leaf00315_log
#print axioms leaf00315_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
