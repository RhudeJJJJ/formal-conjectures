/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00530 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 45351131413092045172262515507200000000000 377570930090448145572324539009951858688 479932508023405285633687552000000000000))
theorem leaf00530_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 45351131413092045172262515507200000000000 377570930090448145572324539009951858688 479932508023405285633687552000000000000 raw00530=true := by decide +kernel
#print axioms leaf00530_raw
theorem leaf00530_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00530=true := by decide +kernel
#print axioms leaf00530_rectangular
def affine00530 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00530 (IntegerComputedClassCell.leftNumerator ![(49/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(49/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(49/3200),0,0] ![(1/3200),1,(1/16)]))
theorem leaf00530_transform : affine00530=(NestedInteger.clearedAll 3 raw00530 (IntegerComputedClassCell.leftNumerator ![(49/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(49/3200),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(49/3200),0,0] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00530_transform
theorem leaf00530_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00530=true := by decide +kernel
#print axioms leaf00530_sign
theorem leaf00530_log : RationalLog.accepts (10006555/2147483648) (-5764717767/2147483648) 8 8=true := by decide +kernel
#print axioms leaf00530_log
def leaf00530 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (196679180811/250000000000) (10006555/2147483648) (-5764717767/2147483648) 8 8 ![60,0,4] ![(49/3200),0,0] ![(1/3200),1,(1/16)] affine00530
theorem leaf00530_checked : FastNestedCellData.accepts 1 2 4 leaf00530=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (196679180811/250000000000) (10006555/2147483648) (-5764717767/2147483648) 8 8 ![60,0,4] ![(49/3200),0,0] ![(1/3200),1,(1/16)] 45351131413092045172262515507200000000000 377570930090448145572324539009951858688 479932508023405285633687552000000000000 raw00530 affine00530
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00530_raw leaf00530_rectangular
    leaf00530_transform leaf00530_sign leaf00530_log
#print axioms leaf00530_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
