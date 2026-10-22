/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00332 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3574541976719581798399937085440000000000 2725251761037076875380858209322837999616 22502249339777046196982214819840000000000))
theorem leaf00332_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3574541976719581798399937085440000000000 2725251761037076875380858209322837999616 22502249339777046196982214819840000000000 raw00332=true := by decide +kernel
#print axioms leaf00332_raw
theorem leaf00332_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00332=true := by decide +kernel
#print axioms leaf00332_rectangular
def affine00332 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00332 (IntegerComputedClassCell.leftNumerator ![(1/128),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/128),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/128),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00332_transform : affine00332=(NestedInteger.clearedAll 3 raw00332 (IntegerComputedClassCell.leftNumerator ![(1/128),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(1/128),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(1/128),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00332_transform
theorem leaf00332_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00332=true := by decide +kernel
#print axioms leaf00332_sign
theorem leaf00332_log : RationalLog.accepts (2920772881/4294967296) (-828060441/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00332_log
def leaf00332 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (4844407721/40000000000) (2920772881/4294967296) (-828060441/4294967296) 1 8 ![60,0,4] ![(1/128),0,(1/8)] ![(1/6400),1,(1/8)] affine00332
theorem leaf00332_checked : FastNestedCellData.accepts 1 2 4 leaf00332=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (4844407721/40000000000) (2920772881/4294967296) (-828060441/4294967296) 1 8 ![60,0,4] ![(1/128),0,(1/8)] ![(1/6400),1,(1/8)] 3574541976719581798399937085440000000000 2725251761037076875380858209322837999616 22502249339777046196982214819840000000000 raw00332 affine00332
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00332_raw leaf00332_rectangular
    leaf00332_transform leaf00332_sign leaf00332_log
#print axioms leaf00332_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
