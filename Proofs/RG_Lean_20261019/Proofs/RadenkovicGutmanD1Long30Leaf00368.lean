/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00368 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 19600344568954567454692999168000000000000 16800045395708801332237960992178374180864 247050932535175113300730970112000000000000))
theorem leaf00368_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 19600344568954567454692999168000000000000 16800045395708801332237960992178374180864 247050932535175113300730970112000000000000 raw00368=true := by decide +kernel
#print axioms leaf00368_raw
theorem leaf00368_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00368=true := by decide +kernel
#print axioms leaf00368_rectangular
def affine00368 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00368 (IntegerComputedClassCell.leftNumerator ![(57/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(57/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(57/6400),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00368_transform : affine00368=(NestedInteger.clearedAll 3 raw00368 (IntegerComputedClassCell.leftNumerator ![(57/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(57/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(57/6400),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00368_transform
theorem leaf00368_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00368=true := by decide +kernel
#print axioms leaf00368_sign
theorem leaf00368_log : RationalLog.accepts (861736341/1073741824) (-118087721/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00368_log
def leaf00368 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (34001177861/500000000000) (861736341/1073741824) (-118087721/1073741824) 1 8 ![60,0,4] ![(57/6400),0,(1/4)] ![(1/6400),1,(1/4)] affine00368
theorem leaf00368_checked : FastNestedCellData.accepts 1 2 4 leaf00368=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (34001177861/500000000000) (861736341/1073741824) (-118087721/1073741824) 1 8 ![60,0,4] ![(57/6400),0,(1/4)] ![(1/6400),1,(1/4)] 19600344568954567454692999168000000000000 16800045395708801332237960992178374180864 247050932535175113300730970112000000000000 raw00368 affine00368
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00368_raw leaf00368_rectangular
    leaf00368_transform leaf00368_sign leaf00368_log
#print axioms leaf00368_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
