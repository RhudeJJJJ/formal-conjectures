/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00165 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 512122956035834278044223143936000000000000 5009789636373862457419198587546227441664 11278334894497077208624922624000000000000))
theorem leaf00165_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 512122956035834278044223143936000000000000 5009789636373862457419198587546227441664 11278334894497077208624922624000000000000 raw00165=true := by decide +kernel
#print axioms leaf00165_raw
theorem leaf00165_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00165=true := by decide +kernel
#print axioms leaf00165_rectangular
def affine00165 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00165 (IntegerComputedClassCell.leftNumerator ![(143/6400),0,0] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(143/6400),0,0] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(143/6400),0,0] ![(3/6400),1,(1/4)]))
theorem leaf00165_transform : affine00165=(NestedInteger.clearedAll 3 raw00165 (IntegerComputedClassCell.leftNumerator ![(143/6400),0,0] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(143/6400),0,0] ![(3/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(143/6400),0,0] ![(3/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00165_transform
theorem leaf00165_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00165=true := by decide +kernel
#print axioms leaf00165_sign
theorem leaf00165_log : RationalLog.accepts (7273091/1073741824) (-5363043647/2147483648) 8 8=true := by decide +kernel
#print axioms leaf00165_log
def leaf00165 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (444195857211/1000000000000) (7273091/1073741824) (-5363043647/2147483648) 8 8 ![52,0,4] ![(143/6400),0,0] ![(3/6400),1,(1/4)] affine00165
theorem leaf00165_checked : FastNestedCellData.accepts 1 0 4 leaf00165=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (444195857211/1000000000000) (7273091/1073741824) (-5363043647/2147483648) 8 8 ![52,0,4] ![(143/6400),0,0] ![(3/6400),1,(1/4)] 512122956035834278044223143936000000000000 5009789636373862457419198587546227441664 11278334894497077208624922624000000000000 raw00165 affine00165
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00165_raw leaf00165_rectangular
    leaf00165_transform leaf00165_sign leaf00165_log
#print axioms leaf00165_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
