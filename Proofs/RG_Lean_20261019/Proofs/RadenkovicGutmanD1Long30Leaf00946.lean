/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00946 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 163868076059518650808267492556800000000000 59293429433921368286646384622085766905856 83433785908888317021319593984000000000000))
theorem leaf00946_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 163868076059518650808267492556800000000000 59293429433921368286646384622085766905856 83433785908888317021319593984000000000000 raw00946=true := by decide +kernel
#print axioms leaf00946_raw
theorem leaf00946_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00946=true := by decide +kernel
#print axioms leaf00946_rectangular
def affine00946 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00946 (IntegerComputedClassCell.leftNumerator ![(3/32),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/32),0,(1/16)] ![(1/320),1,(1/16)]))
theorem leaf00946_transform : affine00946=(NestedInteger.clearedAll 3 raw00946 (IntegerComputedClassCell.leftNumerator ![(3/32),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(3/32),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(3/32),0,(1/16)] ![(1/320),1,(1/16)])) := by decide +kernel
#print axioms leaf00946_transform
theorem leaf00946_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00946=true := by decide +kernel
#print axioms leaf00946_sign
theorem leaf00946_log : RationalLog.accepts (227115745/1073741824) (-3335998017/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00946_log
def leaf00946 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (710664496259/1000000000000) (227115745/1073741824) (-3335998017/4294967296) 3 8 ![60,0,4] ![(3/32),0,(1/16)] ![(1/320),1,(1/16)] affine00946
theorem leaf00946_checked : FastNestedCellData.accepts 1 2 4 leaf00946=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (710664496259/1000000000000) (227115745/1073741824) (-3335998017/4294967296) 3 8 ![60,0,4] ![(3/32),0,(1/16)] ![(1/320),1,(1/16)] 163868076059518650808267492556800000000000 59293429433921368286646384622085766905856 83433785908888317021319593984000000000000 raw00946 affine00946
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00946_raw leaf00946_rectangular
    leaf00946_transform leaf00946_sign leaf00946_log
#print axioms leaf00946_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
