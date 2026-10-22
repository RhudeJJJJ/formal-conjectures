/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00606 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 7279224597159268725337935052800000000000 2457253707391260996832949568066948169728 4864908005847005380499996672000000000000))
theorem leaf00606_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 7279224597159268725337935052800000000000 2457253707391260996832949568066948169728 4864908005847005380499996672000000000000 raw00606=true := by decide +kernel
#print axioms leaf00606_raw
theorem leaf00606_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00606=true := by decide +kernel
#print axioms leaf00606_rectangular
def affine00606 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00606 (IntegerComputedClassCell.leftNumerator ![(1/50),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/50),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/50),0,(1/16)] ![(3/6400),1,(1/16)]))
theorem leaf00606_transform : affine00606=(NestedInteger.clearedAll 3 raw00606 (IntegerComputedClassCell.leftNumerator ![(1/50),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/50),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/50),0,(1/16)] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00606_transform
theorem leaf00606_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00606=true := by decide +kernel
#print axioms leaf00606_sign
theorem leaf00606_log : RationalLog.accepts (963296665/4294967296) (-1605069911/2147483648) 3 8=true := by decide +kernel
#print axioms leaf00606_log
def leaf00606 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (31568604489/62500000000) (963296665/4294967296) (-1605069911/2147483648) 3 8 ![60,0,4] ![(1/50),0,(1/16)] ![(3/6400),1,(1/16)] affine00606
theorem leaf00606_checked : FastNestedCellData.accepts 1 2 4 leaf00606=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (31568604489/62500000000) (963296665/4294967296) (-1605069911/2147483648) 3 8 ![60,0,4] ![(1/50),0,(1/16)] ![(3/6400),1,(1/16)] 7279224597159268725337935052800000000000 2457253707391260996832949568066948169728 4864908005847005380499996672000000000000 raw00606 affine00606
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00606_raw leaf00606_rectangular
    leaf00606_transform leaf00606_sign leaf00606_log
#print axioms leaf00606_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
