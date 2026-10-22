/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00167 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 23344689006815188317724737536000000000000 19497126126724386267094116211074766209024 240725588408676007288290410496000000000000))
theorem leaf00167_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 23344689006815188317724737536000000000000 19497126126724386267094116211074766209024 240725588408676007288290410496000000000000 raw00167=true := by decide +kernel
#print axioms leaf00167_raw
theorem leaf00167_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00167=true := by decide +kernel
#print axioms leaf00167_rectangular
def affine00167 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00167 (IntegerComputedClassCell.leftNumerator ![(143/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(143/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(143/6400),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00167_transform : affine00167=(NestedInteger.clearedAll 3 raw00167 (IntegerComputedClassCell.leftNumerator ![(143/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(143/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(143/6400),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00167_transform
theorem leaf00167_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00167=true := by decide +kernel
#print axioms leaf00167_sign
theorem leaf00167_log : RationalLog.accepts (414791107/536870912) (-138503385/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00167_log
def leaf00167 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (80993160119/1000000000000) (414791107/536870912) (-138503385/1073741824) 1 8 ![52,0,4] ![(143/6400),0,(1/2)] ![(3/6400),1,(1/2)] affine00167
theorem leaf00167_checked : FastNestedCellData.accepts 1 0 4 leaf00167=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (80993160119/1000000000000) (414791107/536870912) (-138503385/1073741824) 1 8 ![52,0,4] ![(143/6400),0,(1/2)] ![(3/6400),1,(1/2)] 23344689006815188317724737536000000000000 19497126126724386267094116211074766209024 240725588408676007288290410496000000000000 raw00167 affine00167
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00167_raw leaf00167_rectangular
    leaf00167_transform leaf00167_sign leaf00167_log
#print axioms leaf00167_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
