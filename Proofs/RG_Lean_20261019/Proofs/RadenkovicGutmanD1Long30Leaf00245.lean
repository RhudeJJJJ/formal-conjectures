/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00245 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 508096912886756969057225801728000000000000 334597111720253848302937787338883858432 759233515688764367641247744000000000000))
theorem leaf00245_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 508096912886756969057225801728000000000000 334597111720253848302937787338883858432 759233515688764367641247744000000000000 raw00245=true := by decide +kernel
#print axioms leaf00245_raw
theorem leaf00245_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00245=true := by decide +kernel
#print axioms leaf00245_rectangular
def affine00245 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00245 (IntegerComputedClassCell.leftNumerator ![(33/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(33/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(33/6400),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00245_transform : affine00245=(NestedInteger.clearedAll 3 raw00245 (IntegerComputedClassCell.leftNumerator ![(33/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(33/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(33/6400),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00245_transform
theorem leaf00245_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00245=true := by decide +kernel
#print axioms leaf00245_sign
theorem leaf00245_log : RationalLog.accepts (1963183/4294967296) (-4128876767/1073741824) 12 8=true := by decide +kernel
#print axioms leaf00245_log
def leaf00245 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (110175955357/250000000000) (1963183/4294967296) (-4128876767/1073741824) 12 8 ![60,0,4] ![(33/6400),0,0] ![(1/6400),1,(1/16)] affine00245
theorem leaf00245_checked : FastNestedCellData.accepts 1 2 4 leaf00245=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (110175955357/250000000000) (1963183/4294967296) (-4128876767/1073741824) 12 8 ![60,0,4] ![(33/6400),0,0] ![(1/6400),1,(1/16)] 508096912886756969057225801728000000000000 334597111720253848302937787338883858432 759233515688764367641247744000000000000 raw00245 affine00245
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00245_raw leaf00245_rectangular
    leaf00245_transform leaf00245_sign leaf00245_log
#print axioms leaf00245_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
