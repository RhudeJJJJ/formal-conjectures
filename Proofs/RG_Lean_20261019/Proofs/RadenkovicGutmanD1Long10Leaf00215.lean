/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00215 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 201250120380954350468238147584000000000000 153107811004057465580145128493072204693504 1169498515881395315842175991808000000000000))
theorem leaf00215_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 201250120380954350468238147584000000000000 153107811004057465580145128493072204693504 1169498515881395315842175991808000000000000 raw00215=true := by decide +kernel
#print axioms leaf00215_raw
theorem leaf00215_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00215=true := by decide +kernel
#print axioms leaf00215_rectangular
def affine00215 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00215 (IntegerComputedClassCell.leftNumerator ![(59/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(59/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(59/1600),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00215_transform : affine00215=(NestedInteger.clearedAll 3 raw00215 (IntegerComputedClassCell.leftNumerator ![(59/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(59/1600),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(59/1600),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00215_transform
theorem leaf00215_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00215=true := by decide +kernel
#print axioms leaf00215_sign
theorem leaf00215_log : RationalLog.accepts (2889283377/4294967296) (-212834663/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00215_log
def leaf00215 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (65458745319/500000000000) (2889283377/4294967296) (-212834663/1073741824) 1 8 ![52,0,4] ![(59/1600),0,(1/2)] ![(3/3200),1,(1/2)] affine00215
theorem leaf00215_checked : FastNestedCellData.accepts 1 0 4 leaf00215=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (65458745319/500000000000) (2889283377/4294967296) (-212834663/1073741824) 1 8 ![52,0,4] ![(59/1600),0,(1/2)] ![(3/3200),1,(1/2)] 201250120380954350468238147584000000000000 153107811004057465580145128493072204693504 1169498515881395315842175991808000000000000 raw00215 affine00215
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00215_raw leaf00215_rectangular
    leaf00215_transform leaf00215_sign leaf00215_log
#print axioms leaf00215_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
