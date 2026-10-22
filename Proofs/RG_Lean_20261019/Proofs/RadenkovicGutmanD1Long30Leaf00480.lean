/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00480 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 848382378867210564236149260288000000000000 4538775623469521273281057429174496526336 6168034781522036167616233472000000000000))
theorem leaf00480_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 848382378867210564236149260288000000000000 4538775623469521273281057429174496526336 6168034781522036167616233472000000000000 raw00480=true := by decide +kernel
#print axioms leaf00480_raw
theorem leaf00480_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00480=true := by decide +kernel
#print axioms leaf00480_rectangular
def affine00480 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00480 (IntegerComputedClassCell.leftNumerator ![(1/80),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/80),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/80),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00480_transform : affine00480=(NestedInteger.clearedAll 3 raw00480 (IntegerComputedClassCell.leftNumerator ![(1/80),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/80),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/80),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00480_transform
theorem leaf00480_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00480=true := by decide +kernel
#print axioms leaf00480_sign
theorem leaf00480_log : RationalLog.accepts (3309281/1073741824) (-12417124247/4294967296) 9 8=true := by decide +kernel
#print axioms leaf00480_log
def leaf00480 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (735854414613/1000000000000) (3309281/1073741824) (-12417124247/4294967296) 9 8 ![60,0,4] ![(1/80),0,0] ![(1/6400),1,(1/16)] affine00480
theorem leaf00480_checked : FastNestedCellData.accepts 1 2 4 leaf00480=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (735854414613/1000000000000) (3309281/1073741824) (-12417124247/4294967296) 9 8 ![60,0,4] ![(1/80),0,0] ![(1/6400),1,(1/16)] 848382378867210564236149260288000000000000 4538775623469521273281057429174496526336 6168034781522036167616233472000000000000 raw00480 affine00480
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00480_raw leaf00480_rectangular
    leaf00480_transform leaf00480_sign leaf00480_log
#print axioms leaf00480_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
