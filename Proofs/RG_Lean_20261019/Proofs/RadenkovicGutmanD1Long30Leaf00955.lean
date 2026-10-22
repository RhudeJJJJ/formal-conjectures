/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00955 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 576834091422521602297348436787200000000000 171879886102245321858679666568880432611328 219863861550030047526805674393600000000000))
theorem leaf00955_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 576834091422521602297348436787200000000000 171879886102245321858679666568880432611328 219863861550030047526805674393600000000000 raw00955=true := by decide +kernel
#print axioms leaf00955_raw
theorem leaf00955_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00955=true := by decide +kernel
#print axioms leaf00955_rectangular
def affine00955 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00955 (IntegerComputedClassCell.leftNumerator ![(1/10),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/10),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/10),0,0] ![(1/320),1,(1/16)]))
theorem leaf00955_transform : affine00955=(NestedInteger.clearedAll 3 raw00955 (IntegerComputedClassCell.leftNumerator ![(1/10),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/10),0,0] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/10),0,0] ![(1/320),1,(1/16)])) := by decide +kernel
#print axioms leaf00955_transform
theorem leaf00955_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00955=true := by decide +kernel
#print axioms leaf00955_sign
theorem leaf00955_log : RationalLog.accepts (718266773/4294967296) (-3840470033/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00955_log
def leaf00955 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (156351193771/200000000000) (718266773/4294967296) (-3840470033/4294967296) 3 8 ![60,0,4] ![(1/10),0,0] ![(1/320),1,(1/16)] affine00955
theorem leaf00955_checked : FastNestedCellData.accepts 1 2 4 leaf00955=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (156351193771/200000000000) (718266773/4294967296) (-3840470033/4294967296) 3 8 ![60,0,4] ![(1/10),0,0] ![(1/320),1,(1/16)] 576834091422521602297348436787200000000000 171879886102245321858679666568880432611328 219863861550030047526805674393600000000000 raw00955 affine00955
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00955_raw leaf00955_rectangular
    leaf00955_transform leaf00955_sign leaf00955_log
#print axioms leaf00955_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
