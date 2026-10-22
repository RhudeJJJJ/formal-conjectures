/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00219 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 311612803030531654787337814016000000000000 299472547865680555532303596488101877252096 17728069558934892409870872477696000000000000))
theorem leaf00219_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 311612803030531654787337814016000000000000 299472547865680555532303596488101877252096 17728069558934892409870872477696000000000000 raw00219=true := by decide +kernel
#print axioms leaf00219_raw
theorem leaf00219_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00219=true := by decide +kernel
#print axioms leaf00219_rectangular
def affine00219 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00219 (IntegerComputedClassCell.leftNumerator ![(29/6400),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(29/6400),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(29/6400),0,(1/2)] ![(3/32000),1,(1/2)]))
theorem leaf00219_transform : affine00219=(NestedInteger.clearedAll 3 raw00219 (IntegerComputedClassCell.leftNumerator ![(29/6400),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(29/6400),0,(1/2)] ![(3/32000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(29/6400),0,(1/2)] ![(3/32000),1,(1/2)])) := by decide +kernel
#print axioms leaf00219_transform
theorem leaf00219_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00219=true := by decide +kernel
#print axioms leaf00219_sign
theorem leaf00219_log : RationalLog.accepts (4059069751/4294967296) (-121311643/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00219_log
def leaf00219 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (16892563901/1000000000000) (4059069751/4294967296) (-121311643/4294967296) 1 8 ![60,0,4] ![(29/6400),0,(1/2)] ![(3/32000),1,(1/2)] affine00219
theorem leaf00219_checked : FastNestedCellData.accepts 1 2 4 leaf00219=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (16892563901/1000000000000) (4059069751/4294967296) (-121311643/4294967296) 1 8 ![60,0,4] ![(29/6400),0,(1/2)] ![(3/32000),1,(1/2)] 311612803030531654787337814016000000000000 299472547865680555532303596488101877252096 17728069558934892409870872477696000000000000 raw00219 affine00219
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00219_raw leaf00219_rectangular
    leaf00219_transform leaf00219_sign leaf00219_log
#print axioms leaf00219_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
