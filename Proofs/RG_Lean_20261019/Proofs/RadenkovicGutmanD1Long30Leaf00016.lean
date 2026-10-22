/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00016 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 442650648287108529736772485120000000000 404237198602877829719251984423791362048 10528703866914900777478651904000000000000))
theorem leaf00016_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 442650648287108529736772485120000000000 404237198602877829719251984423791362048 10528703866914900777478651904000000000000 raw00016=true := by decide +kernel
#print axioms leaf00016_raw
theorem leaf00016_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00016=true := by decide +kernel
#print axioms leaf00016_rectangular
def affine00016 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00016 (IntegerComputedClassCell.leftNumerator ![(19/16000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/16000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/16000),0,(1/16)] ![(1/16000),1,(1/16)]))
theorem leaf00016_transform : affine00016=(NestedInteger.clearedAll 3 raw00016 (IntegerComputedClassCell.leftNumerator ![(19/16000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/16000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/16000),0,(1/16)] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00016_transform
theorem leaf00016_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00016=true := by decide +kernel
#print axioms leaf00016_sign
theorem leaf00016_log : RationalLog.accepts (944306425/1073741824) (-275853207/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00016_log
def leaf00016 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (19196911781/500000000000) (944306425/1073741824) (-275853207/4294967296) 1 8 ![60,0,4] ![(19/16000),0,(1/16)] ![(1/16000),1,(1/16)] affine00016
theorem leaf00016_checked : FastNestedCellData.accepts 1 2 4 leaf00016=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (19196911781/500000000000) (944306425/1073741824) (-275853207/4294967296) 1 8 ![60,0,4] ![(19/16000),0,(1/16)] ![(1/16000),1,(1/16)] 442650648287108529736772485120000000000 404237198602877829719251984423791362048 10528703866914900777478651904000000000000 raw00016 affine00016
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00016_raw leaf00016_rectangular
    leaf00016_transform leaf00016_sign leaf00016_log
#print axioms leaf00016_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
