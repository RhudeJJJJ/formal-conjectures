/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00392 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 686152251719405372475153842176000000000000 493743646524905589790362095304708873781248 3318491873575330698787754606592000000000000))
theorem leaf00392_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 686152251719405372475153842176000000000000 493743646524905589790362095304708873781248 3318491873575330698787754606592000000000000 raw00392=true := by decide +kernel
#print axioms leaf00392_raw
theorem leaf00392_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00392=true := by decide +kernel
#print axioms leaf00392_rectangular
def affine00392 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00392 (IntegerComputedClassCell.leftNumerator ![(31/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(31/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(31/3200),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00392_transform : affine00392=(NestedInteger.clearedAll 3 raw00392 (IntegerComputedClassCell.leftNumerator ![(31/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(31/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(31/3200),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00392_transform
theorem leaf00392_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00392=true := by decide +kernel
#print axioms leaf00392_sign
theorem leaf00392_log : RationalLog.accepts (2690307507/4294967296) (-1004568059/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00392_log
def leaf00392 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (74392776197/500000000000) (2690307507/4294967296) (-1004568059/4294967296) 1 8 ![60,0,4] ![(31/3200),0,(1/8)] ![(1/6400),1,(1/8)] affine00392
theorem leaf00392_checked : FastNestedCellData.accepts 1 2 4 leaf00392=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (74392776197/500000000000) (2690307507/4294967296) (-1004568059/4294967296) 1 8 ![60,0,4] ![(31/3200),0,(1/8)] ![(1/6400),1,(1/8)] 686152251719405372475153842176000000000000 493743646524905589790362095304708873781248 3318491873575330698787754606592000000000000 raw00392 affine00392
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00392_raw leaf00392_rectangular
    leaf00392_transform leaf00392_sign leaf00392_log
#print axioms leaf00392_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
