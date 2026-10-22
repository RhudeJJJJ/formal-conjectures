/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00311 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1018680077497046653712226844672000000000000 623652361782828350363858706275027770146816 2823348508257664298367489933312000000000000))
theorem leaf00311_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1018680077497046653712226844672000000000000 623652361782828350363858706275027770146816 2823348508257664298367489933312000000000000 raw00311=true := by decide +kernel
#print axioms leaf00311_raw
theorem leaf00311_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00311=true := by decide +kernel
#print axioms leaf00311_rectangular
def affine00311 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00311 (IntegerComputedClassCell.leftNumerator ![(23/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/3200),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00311_transform : affine00311=(NestedInteger.clearedAll 3 raw00311 (IntegerComputedClassCell.leftNumerator ![(23/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/3200),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00311_transform
theorem leaf00311_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00311=true := by decide +kernel
#print axioms leaf00311_sign
theorem leaf00311_log : RationalLog.accepts (2153712441/4294967296) (-1482302495/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00311_log
def leaf00311 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (110445515309/500000000000) (2153712441/4294967296) (-1482302495/4294967296) 1 8 ![60,0,4] ![(23/3200),0,(1/16)] ![(1/6400),1,(1/16)] affine00311
theorem leaf00311_checked : FastNestedCellData.accepts 1 2 4 leaf00311=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (110445515309/500000000000) (2153712441/4294967296) (-1482302495/4294967296) 1 8 ![60,0,4] ![(23/3200),0,(1/16)] ![(1/6400),1,(1/16)] 1018680077497046653712226844672000000000000 623652361782828350363858706275027770146816 2823348508257664298367489933312000000000000 raw00311 affine00311
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00311_raw leaf00311_rectangular
    leaf00311_transform leaf00311_sign leaf00311_log
#print axioms leaf00311_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
