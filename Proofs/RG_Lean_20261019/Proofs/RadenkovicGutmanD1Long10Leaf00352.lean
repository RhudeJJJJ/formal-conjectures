/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00352 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2266651230518408126962195234816000000000000 1517446768823255185671710171890254272790528 3087368693193043918577291231232000000000000))
theorem leaf00352_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2266651230518408126962195234816000000000000 1517446768823255185671710171890254272790528 3087368693193043918577291231232000000000000 raw00352=true := by decide +kernel
#print axioms leaf00352_raw
theorem leaf00352_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00352=true := by decide +kernel
#print axioms leaf00352_rectangular
def affine00352 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00352 (IntegerComputedClassCell.leftNumerator ![(7/40),0,(1/4)] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/40),0,(1/4)] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/40),0,(1/4)] ![(1/80),1,(1/4)]))
theorem leaf00352_transform : affine00352=(NestedInteger.clearedAll 3 raw00352 (IntegerComputedClassCell.leftNumerator ![(7/40),0,(1/4)] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/40),0,(1/4)] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/40),0,(1/4)] ![(1/80),1,(1/4)])) := by decide +kernel
#print axioms leaf00352_transform
theorem leaf00352_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00352=true := by decide +kernel
#print axioms leaf00352_sign
theorem leaf00352_log : RationalLog.accepts (963906471/2147483648) (-215032317/536870912) 2 8=true := by decide +kernel
#print axioms leaf00352_log
def leaf00352 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (491501637679/1000000000000) (963906471/2147483648) (-215032317/536870912) 2 8 ![52,0,4] ![(7/40),0,(1/4)] ![(1/80),1,(1/4)] affine00352
theorem leaf00352_checked : FastNestedCellData.accepts 1 0 4 leaf00352=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (491501637679/1000000000000) (963906471/2147483648) (-215032317/536870912) 2 8 ![52,0,4] ![(7/40),0,(1/4)] ![(1/80),1,(1/4)] 2266651230518408126962195234816000000000000 1517446768823255185671710171890254272790528 3087368693193043918577291231232000000000000 raw00352 affine00352
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00352_raw leaf00352_rectangular
    leaf00352_transform leaf00352_sign leaf00352_log
#print axioms leaf00352_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
