/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00745 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 16204874361451160831083237343232000000000000 658897159427677460266559718126905305595904 750052545903732630402684157952000000000000))
theorem leaf00745_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 16204874361451160831083237343232000000000000 658897159427677460266559718126905305595904 750052545903732630402684157952000000000000 raw00745=true := by decide +kernel
#print axioms leaf00745_raw
theorem leaf00745_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00745=true := by decide +kernel
#print axioms leaf00745_rectangular
def affine00745 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00745 (IntegerComputedClassCell.leftNumerator ![(53/1600),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(53/1600),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(53/1600),0,0] ![(3/6400),1,(1/16)]))
theorem leaf00745_transform : affine00745=(NestedInteger.clearedAll 3 raw00745 (IntegerComputedClassCell.leftNumerator ![(53/1600),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(53/1600),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(53/1600),0,0] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00745_transform
theorem leaf00745_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00745=true := by decide +kernel
#print axioms leaf00745_sign
theorem leaf00745_log : RationalLog.accepts (92966831/4294967296) (-514450719/268435456) 6 8=true := by decide +kernel
#print axioms leaf00745_log
def leaf00745 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (878467999377/1000000000000) (92966831/4294967296) (-514450719/268435456) 6 8 ![60,0,4] ![(53/1600),0,0] ![(3/6400),1,(1/16)] affine00745
theorem leaf00745_checked : FastNestedCellData.accepts 1 2 4 leaf00745=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (878467999377/1000000000000) (92966831/4294967296) (-514450719/268435456) 6 8 ![60,0,4] ![(53/1600),0,0] ![(3/6400),1,(1/16)] 16204874361451160831083237343232000000000000 658897159427677460266559718126905305595904 750052545903732630402684157952000000000000 raw00745 affine00745
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00745_raw leaf00745_rectangular
    leaf00745_transform leaf00745_sign leaf00745_log
#print axioms leaf00745_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
