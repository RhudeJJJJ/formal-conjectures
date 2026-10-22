/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00189 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 9769639608060844810437832736768000000000000 185134250308707577149010903990295202889728 349565006666676113174886875136000000000000))
theorem leaf00189_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 9769639608060844810437832736768000000000000 185134250308707577149010903990295202889728 349565006666676113174886875136000000000000 raw00189=true := by decide +kernel
#print axioms leaf00189_raw
theorem leaf00189_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00189=true := by decide +kernel
#print axioms leaf00189_rectangular
def affine00189 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00189 (IntegerComputedClassCell.leftNumerator ![(47/1600),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(47/1600),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(47/1600),0,0] ![(3/3200),1,(1/4)]))
theorem leaf00189_transform : affine00189=(NestedInteger.clearedAll 3 raw00189 (IntegerComputedClassCell.leftNumerator ![(47/1600),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(47/1600),0,0] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(47/1600),0,0] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00189_transform
theorem leaf00189_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00189=true := by decide +kernel
#print axioms leaf00189_sign
theorem leaf00189_log : RationalLog.accepts (53209167/4294967296) (-9429533357/4294967296) 7 8=true := by decide +kernel
#print axioms leaf00189_log
def leaf00189 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (529613224373/1000000000000) (53209167/4294967296) (-9429533357/4294967296) 7 8 ![52,0,4] ![(47/1600),0,0] ![(3/3200),1,(1/4)] affine00189
theorem leaf00189_checked : FastNestedCellData.accepts 1 0 4 leaf00189=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (529613224373/1000000000000) (53209167/4294967296) (-9429533357/4294967296) 7 8 ![52,0,4] ![(47/1600),0,0] ![(3/3200),1,(1/4)] 9769639608060844810437832736768000000000000 185134250308707577149010903990295202889728 349565006666676113174886875136000000000000 raw00189 affine00189
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00189_raw leaf00189_rectangular
    leaf00189_transform leaf00189_sign leaf00189_log
#print axioms leaf00189_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
