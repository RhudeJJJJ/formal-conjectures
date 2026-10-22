/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00355 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 713940878409233197803574919168000000000000 1631314126356427696703178122785940570112 2634359782333669969162665984000000000000))
theorem leaf00355_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 713940878409233197803574919168000000000000 1631314126356427696703178122785940570112 2634359782333669969162665984000000000000 raw00355=true := by decide +kernel
#print axioms leaf00355_raw
theorem leaf00355_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00355=true := by decide +kernel
#print axioms leaf00355_rectangular
def affine00355 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00355 (IntegerComputedClassCell.leftNumerator ![(11/1280),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/1280),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/1280),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00355_transform : affine00355=(NestedInteger.clearedAll 3 raw00355 (IntegerComputedClassCell.leftNumerator ![(11/1280),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/1280),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/1280),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00355_transform
theorem leaf00355_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00355=true := by decide +kernel
#print axioms leaf00355_sign
theorem leaf00355_log : RationalLog.accepts (3030349/2147483648) (-3523684805/1073741824) 10 8=true := by decide +kernel
#print axioms leaf00355_log
def leaf00355 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (309622500559/500000000000) (3030349/2147483648) (-3523684805/1073741824) 10 8 ![60,0,4] ![(11/1280),0,0] ![(1/6400),1,(1/16)] affine00355
theorem leaf00355_checked : FastNestedCellData.accepts 1 2 4 leaf00355=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (309622500559/500000000000) (3030349/2147483648) (-3523684805/1073741824) 10 8 ![60,0,4] ![(11/1280),0,0] ![(1/6400),1,(1/16)] 713940878409233197803574919168000000000000 1631314126356427696703178122785940570112 2634359782333669969162665984000000000000 raw00355 affine00355
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00355_raw leaf00355_rectangular
    leaf00355_transform leaf00355_sign leaf00355_log
#print axioms leaf00355_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
