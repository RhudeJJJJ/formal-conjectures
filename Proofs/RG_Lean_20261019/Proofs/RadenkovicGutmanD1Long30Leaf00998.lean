/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00998 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 21359464268422333864921645711360000000000 13323457875203261661200593409600728858624 28766453890427815238079348736000000000000))
theorem leaf00998_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 21359464268422333864921645711360000000000 13323457875203261661200593409600728858624 28766453890427815238079348736000000000000 raw00998=true := by decide +kernel
#print axioms leaf00998_raw
theorem leaf00998_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00998=true := by decide +kernel
#print axioms leaf00998_rectangular
def affine00998 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00998 (IntegerComputedClassCell.leftNumerator ![(23/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/160),0,(1/4)] ![(1/160),1,(1/4)]))
theorem leaf00998_transform : affine00998=(NestedInteger.clearedAll 3 raw00998 (IntegerComputedClassCell.leftNumerator ![(23/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/160),0,(1/4)] ![(1/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/160),0,(1/4)] ![(1/160),1,(1/4)])) := by decide +kernel
#print axioms leaf00998_transform
theorem leaf00998_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00998=true := by decide +kernel
#print axioms leaf00998_sign
theorem leaf00998_log : RationalLog.accepts (457756775/1073741824) (-1830873493/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00998_log
def leaf00998 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (463159551259/1000000000000) (457756775/1073741824) (-1830873493/4294967296) 2 8 ![60,0,4] ![(23/160),0,(1/4)] ![(1/160),1,(1/4)] affine00998
theorem leaf00998_checked : FastNestedCellData.accepts 1 2 4 leaf00998=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (463159551259/1000000000000) (457756775/1073741824) (-1830873493/4294967296) 2 8 ![60,0,4] ![(23/160),0,(1/4)] ![(1/160),1,(1/4)] 21359464268422333864921645711360000000000 13323457875203261661200593409600728858624 28766453890427815238079348736000000000000 raw00998 affine00998
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00998_raw leaf00998_rectangular
    leaf00998_transform leaf00998_sign leaf00998_log
#print axioms leaf00998_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
