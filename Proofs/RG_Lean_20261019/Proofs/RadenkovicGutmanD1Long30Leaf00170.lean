/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00170 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1250462739766838991152742400000000000 344158235256933073579568573448192 1032918222169908340326400000000000))
theorem leaf00170_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1250462739766838991152742400000000000 344158235256933073579568573448192 1032918222169908340326400000000000 raw00170=true := by decide +kernel
#print axioms leaf00170_raw
theorem leaf00170_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00170=true := by decide +kernel
#print axioms leaf00170_rectangular
def affine00170 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00170 (IntegerComputedClassCell.leftNumerator ![(59/16000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(59/16000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(59/16000),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00170_transform : affine00170=(NestedInteger.clearedAll 3 raw00170 (IntegerComputedClassCell.leftNumerator ![(59/16000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(59/16000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(59/16000),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00170_transform
theorem leaf00170_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00170=true := by decide +kernel
#print axioms leaf00170_sign
theorem leaf00170_log : RationalLog.accepts (6927/33554432) (-18222467405/4294967296) 13 8=true := by decide +kernel
#print axioms leaf00170_log
def leaf00170 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (33319020603/100000000000) (6927/33554432) (-18222467405/4294967296) 13 8 ![60,0,4] ![(59/16000),0,0] ![(3/32000),1,(1/16)] affine00170
theorem leaf00170_checked : FastNestedCellData.accepts 1 2 4 leaf00170=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (33319020603/100000000000) (6927/33554432) (-18222467405/4294967296) 13 8 ![60,0,4] ![(59/16000),0,0] ![(3/32000),1,(1/16)] 1250462739766838991152742400000000000 344158235256933073579568573448192 1032918222169908340326400000000000 raw00170 affine00170
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00170_raw leaf00170_rectangular
    leaf00170_transform leaf00170_sign leaf00170_log
#print axioms leaf00170_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
