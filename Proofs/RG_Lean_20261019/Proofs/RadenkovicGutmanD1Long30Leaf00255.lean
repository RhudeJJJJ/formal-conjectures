/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00255 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2124758883183108160216706842624000000000000 1622841268396204857027852688569193725952 3522298199021006003101499392000000000000))
theorem leaf00255_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2124758883183108160216706842624000000000000 1622841268396204857027852688569193725952 3522298199021006003101499392000000000000 raw00255=true := by decide +kernel
#print axioms leaf00255_raw
theorem leaf00255_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00255=true := by decide +kernel
#print axioms leaf00255_rectangular
def affine00255 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00255 (IntegerComputedClassCell.leftNumerator ![(7/1280),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/1280),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/1280),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00255_transform : affine00255=(NestedInteger.clearedAll 3 raw00255 (IntegerComputedClassCell.leftNumerator ![(7/1280),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/1280),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/1280),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00255_transform
theorem leaf00255_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00255=true := by decide +kernel
#print axioms leaf00255_sign
theorem leaf00255_log : RationalLog.accepts (1122859/2147483648) (-4056690085/1073741824) 11 8=true := by decide +kernel
#print axioms leaf00255_log
def leaf00255 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (460733639431/1000000000000) (1122859/2147483648) (-4056690085/1073741824) 11 8 ![60,0,4] ![(7/1280),0,0] ![(1/6400),1,(1/16)] affine00255
theorem leaf00255_checked : FastNestedCellData.accepts 1 2 4 leaf00255=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (460733639431/1000000000000) (1122859/2147483648) (-4056690085/1073741824) 11 8 ![60,0,4] ![(7/1280),0,0] ![(1/6400),1,(1/16)] 2124758883183108160216706842624000000000000 1622841268396204857027852688569193725952 3522298199021006003101499392000000000000 raw00255 affine00255
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00255_raw leaf00255_rectangular
    leaf00255_transform leaf00255_sign leaf00255_log
#print axioms leaf00255_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
