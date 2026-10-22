/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00931 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 649201085386739102089058713600000000000 215169114161010722317150830037252964352 298531707407697317927583744000000000000))
theorem leaf00931_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 649201085386739102089058713600000000000 215169114161010722317150830037252964352 298531707407697317927583744000000000000 raw00931=true := by decide +kernel
#print axioms leaf00931_raw
theorem leaf00931_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00931=true := by decide +kernel
#print axioms leaf00931_rectangular
def affine00931 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00931 (IntegerComputedClassCell.leftNumerator ![(27/320),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(27/320),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(27/320),0,(1/16)] ![(1/320),1,(1/16)]))
theorem leaf00931_transform : affine00931=(NestedInteger.clearedAll 3 raw00931 (IntegerComputedClassCell.leftNumerator ![(27/320),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(27/320),0,(1/16)] ![(1/320),1,(1/16)]) (IntegerComputedClassCell.denominator ![(27/320),0,(1/16)] ![(1/320),1,(1/16)])) := by decide +kernel
#print axioms leaf00931_transform
theorem leaf00931_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00931=true := by decide +kernel
#print axioms leaf00931_sign
theorem leaf00931_log : RationalLog.accepts (413628795/2147483648) (-3537084127/4294967296) 3 8=true := by decide +kernel
#print axioms leaf00931_log
def leaf00931 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (22523687269/31250000000) (413628795/2147483648) (-3537084127/4294967296) 3 8 ![60,0,4] ![(27/320),0,(1/16)] ![(1/320),1,(1/16)] affine00931
theorem leaf00931_checked : FastNestedCellData.accepts 1 2 4 leaf00931=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (22523687269/31250000000) (413628795/2147483648) (-3537084127/4294967296) 3 8 ![60,0,4] ![(27/320),0,(1/16)] ![(1/320),1,(1/16)] 649201085386739102089058713600000000000 215169114161010722317150830037252964352 298531707407697317927583744000000000000 raw00931 affine00931
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00931_raw leaf00931_rectangular
    leaf00931_transform leaf00931_sign leaf00931_log
#print axioms leaf00931_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
