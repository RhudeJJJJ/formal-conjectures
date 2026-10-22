/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00120 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 5652899105864816897918800756736000000000000 16023316836276559201079487356582812975104 52287864926528822424763367424000000000000))
theorem leaf00120_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 5652899105864816897918800756736000000000000 16023316836276559201079487356582812975104 52287864926528822424763367424000000000000 raw00120=true := by decide +kernel
#print axioms leaf00120_raw
theorem leaf00120_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00120=true := by decide +kernel
#print axioms leaf00120_rectangular
def affine00120 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00120 (IntegerComputedClassCell.leftNumerator ![(11/800),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/800),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/800),0,0] ![(1/1600),1,(1/4)]))
theorem leaf00120_transform : affine00120=(NestedInteger.clearedAll 3 raw00120 (IntegerComputedClassCell.leftNumerator ![(11/800),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/800),0,0] ![(1/1600),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/800),0,0] ![(1/1600),1,(1/4)])) := by decide +kernel
#print axioms leaf00120_transform
theorem leaf00120_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00120=true := by decide +kernel
#print axioms leaf00120_sign
theorem leaf00120_log : RationalLog.accepts (9318589/4294967296) (-13170921253/4294967296) 9 8=true := by decide +kernel
#print axioms leaf00120_log
def leaf00120 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (306444274571/1000000000000) (9318589/4294967296) (-13170921253/4294967296) 9 8 ![52,0,4] ![(11/800),0,0] ![(1/1600),1,(1/4)] affine00120
theorem leaf00120_checked : FastNestedCellData.accepts 1 0 4 leaf00120=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (306444274571/1000000000000) (9318589/4294967296) (-13170921253/4294967296) 9 8 ![52,0,4] ![(11/800),0,0] ![(1/1600),1,(1/4)] 5652899105864816897918800756736000000000000 16023316836276559201079487356582812975104 52287864926528822424763367424000000000000 raw00120 affine00120
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00120_raw leaf00120_rectangular
    leaf00120_transform leaf00120_sign leaf00120_log
#print axioms leaf00120_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
