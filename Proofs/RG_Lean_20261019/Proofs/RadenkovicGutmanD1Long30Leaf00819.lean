/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00819 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2925207699030323185635565764608000000000000 2138030704167979542476003135881462004318208 13482702522146923171798440738816000000000000))
theorem leaf00819_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2925207699030323185635565764608000000000000 2138030704167979542476003135881462004318208 13482702522146923171798440738816000000000000 raw00819=true := by decide +kernel
#print axioms leaf00819_raw
theorem leaf00819_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00819=true := by decide +kernel
#print axioms leaf00819_rectangular
def affine00819 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00819 (IntegerComputedClassCell.leftNumerator ![(29/640),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(29/640),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(29/640),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00819_transform : affine00819=(NestedInteger.clearedAll 3 raw00819 (IntegerComputedClassCell.leftNumerator ![(29/640),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(29/640),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(29/640),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00819_transform
theorem leaf00819_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00819=true := by decide +kernel
#print axioms leaf00819_sign
theorem leaf00819_log : RationalLog.accepts (2709521667/4294967296) (-494642627/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00819_log
def leaf00819 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (158575827113/1000000000000) (2709521667/4294967296) (-494642627/2147483648) 1 8 ![60,0,4] ![(29/640),0,(1/2)] ![(3/3200),1,(1/2)] affine00819
theorem leaf00819_checked : FastNestedCellData.accepts 1 2 4 leaf00819=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (158575827113/1000000000000) (2709521667/4294967296) (-494642627/2147483648) 1 8 ![60,0,4] ![(29/640),0,(1/2)] ![(3/3200),1,(1/2)] 2925207699030323185635565764608000000000000 2138030704167979542476003135881462004318208 13482702522146923171798440738816000000000000 raw00819 affine00819
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00819_raw leaf00819_rectangular
    leaf00819_transform leaf00819_sign leaf00819_log
#print axioms leaf00819_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
