/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00365 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 11647156186923091708832605274112000000000000 28924449633352706616199226276567826038784 45810488955099530365147021312000000000000))
theorem leaf00365_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 11647156186923091708832605274112000000000000 28924449633352706616199226276567826038784 45810488955099530365147021312000000000000 raw00365=true := by decide +kernel
#print axioms leaf00365_raw
theorem leaf00365_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00365=true := by decide +kernel
#print axioms leaf00365_rectangular
def affine00365 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00365 (IntegerComputedClassCell.leftNumerator ![(57/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(57/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(57/6400),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00365_transform : affine00365=(NestedInteger.clearedAll 3 raw00365 (IntegerComputedClassCell.leftNumerator ![(57/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(57/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(57/6400),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00365_transform
theorem leaf00365_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00365=true := by decide +kernel
#print axioms leaf00365_sign
theorem leaf00365_log : RationalLog.accepts (6538021/4294967296) (-13931939461/4294967296) 10 8=true := by decide +kernel
#print axioms leaf00365_log
def leaf00365 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (631393602057/1000000000000) (6538021/4294967296) (-13931939461/4294967296) 10 8 ![60,0,4] ![(57/6400),0,0] ![(1/6400),1,(1/16)] affine00365
theorem leaf00365_checked : FastNestedCellData.accepts 1 2 4 leaf00365=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (631393602057/1000000000000) (6538021/4294967296) (-13931939461/4294967296) 10 8 ![60,0,4] ![(57/6400),0,0] ![(1/6400),1,(1/16)] 11647156186923091708832605274112000000000000 28924449633352706616199226276567826038784 45810488955099530365147021312000000000000 raw00365 affine00365
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00365_raw leaf00365_rectangular
    leaf00365_transform leaf00365_sign leaf00365_log
#print axioms leaf00365_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
