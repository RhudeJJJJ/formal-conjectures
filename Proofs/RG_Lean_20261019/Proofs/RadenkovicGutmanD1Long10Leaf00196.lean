/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00196 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 258533838673891417903245295616000000000000 162860705154831521757027511953169745707008 726270921406476379137075314688000000000000))
theorem leaf00196_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 258533838673891417903245295616000000000000 162860705154831521757027511953169745707008 726270921406476379137075314688000000000000 raw00196=true := by decide +kernel
#print axioms leaf00196_raw
theorem leaf00196_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00196=true := by decide +kernel
#print axioms leaf00196_rectangular
def affine00196 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00196 (IntegerComputedClassCell.leftNumerator ![(1/32),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/32),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/32),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00196_transform : affine00196=(NestedInteger.clearedAll 3 raw00196 (IntegerComputedClassCell.leftNumerator ![(1/32),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/32),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/32),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00196_transform
theorem leaf00196_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00196=true := by decide +kernel
#print axioms leaf00196_sign
theorem leaf00196_log : RationalLog.accepts (552498857/1073741824) (-1426903049/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00196_log
def leaf00196 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (224242359641/1000000000000) (552498857/1073741824) (-1426903049/4294967296) 1 8 ![52,0,4] ![(1/32),0,(1/4)] ![(3/3200),1,(1/4)] affine00196
theorem leaf00196_checked : FastNestedCellData.accepts 1 0 4 leaf00196=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (224242359641/1000000000000) (552498857/1073741824) (-1426903049/4294967296) 1 8 ![52,0,4] ![(1/32),0,(1/4)] ![(3/3200),1,(1/4)] 258533838673891417903245295616000000000000 162860705154831521757027511953169745707008 726270921406476379137075314688000000000000 raw00196 affine00196
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00196_raw leaf00196_rectangular
    leaf00196_transform leaf00196_sign leaf00196_log
#print axioms leaf00196_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
