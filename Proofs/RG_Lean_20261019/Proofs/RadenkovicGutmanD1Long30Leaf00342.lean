/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00342 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 28999344953277486555221668659200000000000 21893716418006325567183436275068161753088 174084873398015681702163120128000000000000))
theorem leaf00342_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 28999344953277486555221668659200000000000 21893716418006325567183436275068161753088 174084873398015681702163120128000000000000 raw00342=true := by decide +kernel
#print axioms leaf00342_raw
theorem leaf00342_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00342=true := by decide +kernel
#print axioms leaf00342_rectangular
def affine00342 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00342 (IntegerComputedClassCell.leftNumerator ![(13/1600),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(13/1600),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(13/1600),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00342_transform : affine00342=(NestedInteger.clearedAll 3 raw00342 (IntegerComputedClassCell.leftNumerator ![(13/1600),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(13/1600),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(13/1600),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00342_transform
theorem leaf00342_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00342=true := by decide +kernel
#print axioms leaf00342_sign
theorem leaf00342_log : RationalLog.accepts (2880338765/4294967296) (-857997121/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00342_log
def leaf00342 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (31441152799/250000000000) (2880338765/4294967296) (-857997121/4294967296) 1 8 ![60,0,4] ![(13/1600),0,(1/8)] ![(1/6400),1,(1/8)] affine00342
theorem leaf00342_checked : FastNestedCellData.accepts 1 2 4 leaf00342=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (31441152799/250000000000) (2880338765/4294967296) (-857997121/4294967296) 1 8 ![60,0,4] ![(13/1600),0,(1/8)] ![(1/6400),1,(1/8)] 28999344953277486555221668659200000000000 21893716418006325567183436275068161753088 174084873398015681702163120128000000000000 raw00342 affine00342
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00342_raw leaf00342_rectangular
    leaf00342_transform leaf00342_sign leaf00342_log
#print axioms leaf00342_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
