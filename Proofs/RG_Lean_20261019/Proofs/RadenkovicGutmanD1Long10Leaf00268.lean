/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00268 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 6634885396668190516027020279808000000000000 3496984521396783018130131041084615096795136 9722546003330187258622768054272000000000000))
theorem leaf00268_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 6634885396668190516027020279808000000000000 3496984521396783018130131041084615096795136 9722546003330187258622768054272000000000000 raw00268=true := by decide +kernel
#print axioms leaf00268_raw
theorem leaf00268_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00268=true := by decide +kernel
#print axioms leaf00268_rectangular
def affine00268 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00268 (IntegerComputedClassCell.leftNumerator ![(37/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/640),0,(1/4)] ![(1/640),1,(1/4)]))
theorem leaf00268_transform : affine00268=(NestedInteger.clearedAll 3 raw00268 (IntegerComputedClassCell.leftNumerator ![(37/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/640),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/640),0,(1/4)] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00268_transform
theorem leaf00268_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00268=true := by decide +kernel
#print axioms leaf00268_sign
theorem leaf00268_log : RationalLog.accepts (1664884539/4294967296) (-2035144911/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00268_log
def leaf00268 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (359677858063/1000000000000) (1664884539/4294967296) (-2035144911/4294967296) 2 8 ![52,0,4] ![(37/640),0,(1/4)] ![(1/640),1,(1/4)] affine00268
theorem leaf00268_checked : FastNestedCellData.accepts 1 0 4 leaf00268=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (359677858063/1000000000000) (1664884539/4294967296) (-2035144911/4294967296) 2 8 ![52,0,4] ![(37/640),0,(1/4)] ![(1/640),1,(1/4)] 6634885396668190516027020279808000000000000 3496984521396783018130131041084615096795136 9722546003330187258622768054272000000000000 raw00268 affine00268
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00268_raw leaf00268_rectangular
    leaf00268_transform leaf00268_sign leaf00268_log
#print axioms leaf00268_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
