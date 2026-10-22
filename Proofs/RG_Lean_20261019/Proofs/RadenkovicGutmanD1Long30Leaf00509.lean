/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00509 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 855795011803857304177921228800000000000 761807376743280297953657963948562972672 14928028662788479344880019046400000000000))
theorem leaf00509_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 855795011803857304177921228800000000000 761807376743280297953657963948562972672 14928028662788479344880019046400000000000 raw00509=true := by decide +kernel
#print axioms leaf00509_raw
theorem leaf00509_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00509=true := by decide +kernel
#print axioms leaf00509_rectangular
def affine00509 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00509 (IntegerComputedClassCell.leftNumerator ![(11/800),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/800),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/800),0,(1/2)] ![(1/3200),1,(1/2)]))
theorem leaf00509_transform : affine00509=(NestedInteger.clearedAll 3 raw00509 (IntegerComputedClassCell.leftNumerator ![(11/800),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/800),0,(1/2)] ![(1/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/800),0,(1/2)] ![(1/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00509_transform
theorem leaf00509_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00509=true := by decide +kernel
#print axioms leaf00509_sign
theorem leaf00509_log : RationalLog.accepts (1818818419/2147483648) (-44589735/536870912) 1 8=true := by decide +kernel
#print axioms leaf00509_log
def leaf00509 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (10206402921/200000000000) (1818818419/2147483648) (-44589735/536870912) 1 8 ![60,0,4] ![(11/800),0,(1/2)] ![(1/3200),1,(1/2)] affine00509
theorem leaf00509_checked : FastNestedCellData.accepts 1 2 4 leaf00509=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (10206402921/200000000000) (1818818419/2147483648) (-44589735/536870912) 1 8 ![60,0,4] ![(11/800),0,(1/2)] ![(1/3200),1,(1/2)] 855795011803857304177921228800000000000 761807376743280297953657963948562972672 14928028662788479344880019046400000000000 raw00509 affine00509
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00509_raw leaf00509_rectangular
    leaf00509_transform leaf00509_sign leaf00509_log
#print axioms leaf00509_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
