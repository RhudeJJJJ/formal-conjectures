/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00432 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 769557702953371618030246690816000000000000 533544204863979237971708564896935674118144 3197340940570453646240787726336000000000000))
theorem leaf00432_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 769557702953371618030246690816000000000000 533544204863979237971708564896935674118144 3197340940570453646240787726336000000000000 raw00432=true := by decide +kernel
#print axioms leaf00432_raw
theorem leaf00432_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00432=true := by decide +kernel
#print axioms leaf00432_rectangular
def affine00432 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00432 (IntegerComputedClassCell.leftNumerator ![(7/640),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/640),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/640),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00432_transform : affine00432=(NestedInteger.clearedAll 3 raw00432 (IntegerComputedClassCell.leftNumerator ![(7/640),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(7/640),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(7/640),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00432_transform
theorem leaf00432_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00432=true := by decide +kernel
#print axioms leaf00432_sign
theorem leaf00432_log : RationalLog.accepts (1275957333/2147483648) (-1117980053/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00432_log
def leaf00432 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (166871226679/1000000000000) (1275957333/2147483648) (-1117980053/4294967296) 1 8 ![60,0,4] ![(7/640),0,(1/8)] ![(1/6400),1,(1/8)] affine00432
theorem leaf00432_checked : FastNestedCellData.accepts 1 2 4 leaf00432=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (166871226679/1000000000000) (1275957333/2147483648) (-1117980053/4294967296) 1 8 ![60,0,4] ![(7/640),0,(1/8)] ![(1/6400),1,(1/8)] 769557702953371618030246690816000000000000 533544204863979237971708564896935674118144 3197340940570453646240787726336000000000000 raw00432 affine00432
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00432_raw leaf00432_rectangular
    leaf00432_transform leaf00432_sign leaf00432_log
#print axioms leaf00432_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
