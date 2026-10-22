/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00176 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 16592721538049233977208943411200000000000 13576797382244307750884993661993660448768 150938293080229120347306616422400000000000))
theorem leaf00176_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 16592721538049233977208943411200000000000 13576797382244307750884993661993660448768 150938293080229120347306616422400000000000 raw00176=true := by decide +kernel
#print axioms leaf00176_raw
theorem leaf00176_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00176=true := by decide +kernel
#print axioms leaf00176_rectangular
def affine00176 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00176 (IntegerComputedClassCell.leftNumerator ![(79/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(79/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(79/3200),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00176_transform : affine00176=(NestedInteger.clearedAll 3 raw00176 (IntegerComputedClassCell.leftNumerator ![(79/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(79/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(79/3200),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00176_transform
theorem leaf00176_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00176=true := by decide +kernel
#print axioms leaf00176_sign
theorem leaf00176_log : RationalLog.accepts (1612141921/2147483648) (-153938659/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00176_log
def leaf00176 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (17989864739/200000000000) (1612141921/2147483648) (-153938659/1073741824) 1 8 ![52,0,4] ![(79/3200),0,(1/2)] ![(3/3200),1,(1/2)] affine00176
theorem leaf00176_checked : FastNestedCellData.accepts 1 0 4 leaf00176=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (17989864739/200000000000) (1612141921/2147483648) (-153938659/1073741824) 1 8 ![52,0,4] ![(79/3200),0,(1/2)] ![(3/3200),1,(1/2)] 16592721538049233977208943411200000000000 13576797382244307750884993661993660448768 150938293080229120347306616422400000000000 raw00176 affine00176
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00176_raw leaf00176_rectangular
    leaf00176_transform leaf00176_sign leaf00176_log
#print axioms leaf00176_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
