/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00736 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 11509280956566522920920154112000000000000 3045148195365460169973752186873460031488 4766284993715908850499977216000000000000))
theorem leaf00736_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 11509280956566522920920154112000000000000 3045148195365460169973752186873460031488 4766284993715908850499977216000000000000 raw00736=true := by decide +kernel
#print axioms leaf00736_raw
theorem leaf00736_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00736=true := by decide +kernel
#print axioms leaf00736_rectangular
def affine00736 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00736 (IntegerComputedClassCell.leftNumerator ![(103/3200),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(103/3200),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(103/3200),0,(1/16)] ![(3/6400),1,(1/16)]))
theorem leaf00736_transform : affine00736=(NestedInteger.clearedAll 3 raw00736 (IntegerComputedClassCell.leftNumerator ![(103/3200),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(103/3200),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(103/3200),0,(1/16)] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00736_transform
theorem leaf00736_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00736=true := by decide +kernel
#print axioms leaf00736_sign
theorem leaf00736_log : RationalLog.accepts (21668029/134217728) (-979051491/1073741824) 3 8=true := by decide +kernel
#print axioms leaf00736_log
def leaf00736 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (638893435743/1000000000000) (21668029/134217728) (-979051491/1073741824) 3 8 ![60,0,4] ![(103/3200),0,(1/16)] ![(3/6400),1,(1/16)] affine00736
theorem leaf00736_checked : FastNestedCellData.accepts 1 2 4 leaf00736=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (638893435743/1000000000000) (21668029/134217728) (-979051491/1073741824) 3 8 ![60,0,4] ![(103/3200),0,(1/16)] ![(3/6400),1,(1/16)] 11509280956566522920920154112000000000000 3045148195365460169973752186873460031488 4766284993715908850499977216000000000000 raw00736 affine00736
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00736_raw leaf00736_rectangular
    leaf00736_transform leaf00736_sign leaf00736_log
#print axioms leaf00736_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
