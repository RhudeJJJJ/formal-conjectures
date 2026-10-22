/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00873 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4138857232710899293231670886400000000000 2214737889889936242791875149637538021376 6169381538800364643877807718400000000000))
theorem leaf00873_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4138857232710899293231670886400000000000 2214737889889936242791875149637538021376 6169381538800364643877807718400000000000 raw00873=true := by decide +kernel
#print axioms leaf00873_raw
theorem leaf00873_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00873=true := by decide +kernel
#print axioms leaf00873_rectangular
def affine00873 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00873 (IntegerComputedClassCell.leftNumerator ![(19/320),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/320),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/320),0,(1/4)] ![(1/640),1,(1/4)]))
theorem leaf00873_transform : affine00873=(NestedInteger.clearedAll 3 raw00873 (IntegerComputedClassCell.leftNumerator ![(19/320),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/320),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/320),0,(1/4)] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00873_transform
theorem leaf00873_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00873=true := by decide +kernel
#print axioms leaf00873_sign
theorem leaf00873_log : RationalLog.accepts (211395597/536870912) (-2001511595/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00873_log
def leaf00873 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (71797728053/200000000000) (211395597/536870912) (-2001511595/4294967296) 2 8 ![60,0,4] ![(19/320),0,(1/4)] ![(1/640),1,(1/4)] affine00873
theorem leaf00873_checked : FastNestedCellData.accepts 1 2 4 leaf00873=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (71797728053/200000000000) (211395597/536870912) (-2001511595/4294967296) 2 8 ![60,0,4] ![(19/320),0,(1/4)] ![(1/640),1,(1/4)] 4138857232710899293231670886400000000000 2214737889889936242791875149637538021376 6169381538800364643877807718400000000000 raw00873 affine00873
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00873_raw leaf00873_rectangular
    leaf00873_transform leaf00873_sign leaf00873_log
#print axioms leaf00873_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
