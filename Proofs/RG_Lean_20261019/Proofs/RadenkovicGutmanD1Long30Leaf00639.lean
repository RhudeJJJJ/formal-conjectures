/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00639 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 735095485349302438442313973760000000000 611804367831432595276546793631085756416 7310873097437076288528449536000000000000))
theorem leaf00639_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 735095485349302438442313973760000000000 611804367831432595276546793631085756416 7310873097437076288528449536000000000000 raw00639=true := by decide +kernel
#print axioms leaf00639_raw
theorem leaf00639_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00639=true := by decide +kernel
#print axioms leaf00639_rectangular
def affine00639 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00639 (IntegerComputedClassCell.leftNumerator ![(73/3200),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(73/3200),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(73/3200),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00639_transform : affine00639=(NestedInteger.clearedAll 3 raw00639 (IntegerComputedClassCell.leftNumerator ![(73/3200),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(73/3200),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(73/3200),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00639_transform
theorem leaf00639_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00639=true := by decide +kernel
#print axioms leaf00639_sign
theorem leaf00639_log : RationalLog.accepts (1649285925/2147483648) (-283418831/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00639_log
def leaf00639 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (83684172831/1000000000000) (1649285925/2147483648) (-283418831/2147483648) 1 8 ![60,0,4] ![(73/3200),0,(1/2)] ![(3/6400),1,(1/2)] affine00639
theorem leaf00639_checked : FastNestedCellData.accepts 1 2 4 leaf00639=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (83684172831/1000000000000) (1649285925/2147483648) (-283418831/2147483648) 1 8 ![60,0,4] ![(73/3200),0,(1/2)] ![(3/6400),1,(1/2)] 735095485349302438442313973760000000000 611804367831432595276546793631085756416 7310873097437076288528449536000000000000 raw00639 affine00639
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00639_raw leaf00639_rectangular
    leaf00639_transform leaf00639_sign leaf00639_log
#print axioms leaf00639_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
