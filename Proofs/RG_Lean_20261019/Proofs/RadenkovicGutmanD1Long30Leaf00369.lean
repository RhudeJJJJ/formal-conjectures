/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00369 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 610365876783785543324502327296000000000000 565446943675879951099965407681540536664064 17089184461314743266669907410944000000000000))
theorem leaf00369_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 610365876783785543324502327296000000000000 565446943675879951099965407681540536664064 17089184461314743266669907410944000000000000 raw00369=true := by decide +kernel
#print axioms leaf00369_raw
theorem leaf00369_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00369=true := by decide +kernel
#print axioms leaf00369_rectangular
def affine00369 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00369 (IntegerComputedClassCell.leftNumerator ![(57/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(57/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(57/6400),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00369_transform : affine00369=(NestedInteger.clearedAll 3 raw00369 (IntegerComputedClassCell.leftNumerator ![(57/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(57/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(57/6400),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00369_transform
theorem leaf00369_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00369=true := by decide +kernel
#print axioms leaf00369_sign
theorem leaf00369_log : RationalLog.accepts (3851449069/4294967296) (-7314497/134217728) 1 8=true := by decide +kernel
#print axioms leaf00369_log
def leaf00369 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (33088000481/1000000000000) (3851449069/4294967296) (-7314497/134217728) 1 8 ![60,0,4] ![(57/6400),0,(1/2)] ![(1/6400),1,(1/2)] affine00369
theorem leaf00369_checked : FastNestedCellData.accepts 1 2 4 leaf00369=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (33088000481/1000000000000) (3851449069/4294967296) (-7314497/134217728) 1 8 ![60,0,4] ![(57/6400),0,(1/2)] ![(1/6400),1,(1/2)] 610365876783785543324502327296000000000000 565446943675879951099965407681540536664064 17089184461314743266669907410944000000000000 raw00369 affine00369
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00369_raw leaf00369_rectangular
    leaf00369_transform leaf00369_sign leaf00369_log
#print axioms leaf00369_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
