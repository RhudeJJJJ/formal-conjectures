/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00936 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1103258521579832341376719126528000000000000 376564640743697469764245197446785013907456 524687506685524935995174158336000000000000))
theorem leaf00936_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1103258521579832341376719126528000000000000 376564640743697469764245197446785013907456 524687506685524935995174158336000000000000 raw00936=true := by decide +kernel
#print axioms leaf00936_raw
theorem leaf00936_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00936=true := by decide +kernel
#print axioms leaf00936_rectangular
def affine00936 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00936 (IntegerComputedClassCell.leftNumerator ![(7/80),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/80),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/80),0,(1/16)] ![(1/320),1,(1/16)]))
theorem leaf00936_transform : affine00936=(NestedInteger.clearedAll 3 raw00936 (IntegerComputedClassCell.leftNumerator ![(7/80),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/80),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/80),0,(1/16)] ![(1/320),1,(1/16)])) := by decide +kernel
#print axioms leaf00936_transform
theorem leaf00936_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00936=true := by decide +kernel
#print axioms leaf00936_sign
theorem leaf00936_log : RationalLog.accepts (853446927/4294967296) (-3470152997/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00936_log
def leaf00936 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (358846585773/500000000000) (853446927/4294967296) (-3470152997/4294967296) 3 8 ![60,0,4] ![(7/80),0,(1/16)] ![(1/320),1,(1/16)] affine00936
theorem leaf00936_checked : FastNestedCellData.accepts 1 2 4 leaf00936=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (358846585773/500000000000) (853446927/4294967296) (-3470152997/4294967296) 3 8 ![60,0,4] ![(7/80),0,(1/16)] ![(1/320),1,(1/16)] 1103258521579832341376719126528000000000000 376564640743697469764245197446785013907456 524687506685524935995174158336000000000000 raw00936 affine00936
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00936_raw leaf00936_rectangular
    leaf00936_transform leaf00936_sign leaf00936_log
#print axioms leaf00936_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
