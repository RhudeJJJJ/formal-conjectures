/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00293 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 29061008056983261357650477056000000000 25875116435593143473457239891329941504 513264682944005437120315392000000000000))
theorem leaf00293_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 29061008056983261357650477056000000000 25875116435593143473457239891329941504 513264682944005437120315392000000000000 raw00293=true := by decide +kernel
#print axioms leaf00293_raw
theorem leaf00293_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00293=true := by decide +kernel
#print axioms leaf00293_rectangular
def affine00293 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00293 (IntegerComputedClassCell.leftNumerator ![(21/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(21/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(21/3200),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00293_transform : affine00293=(NestedInteger.clearedAll 3 raw00293 (IntegerComputedClassCell.leftNumerator ![(21/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(21/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(21/3200),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00293_transform
theorem leaf00293_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00293=true := by decide +kernel
#print axioms leaf00293_sign
theorem leaf00293_log : RationalLog.accepts (3640587625/4294967296) (-354976585/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00293_log
def leaf00293 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (3150800807/62500000000) (3640587625/4294967296) (-354976585/4294967296) 1 8 ![60,0,4] ![(21/3200),0,(1/4)] ![(1/6400),1,(1/4)] affine00293
theorem leaf00293_checked : FastNestedCellData.accepts 1 2 4 leaf00293=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (3150800807/62500000000) (3640587625/4294967296) (-354976585/4294967296) 1 8 ![60,0,4] ![(21/3200),0,(1/4)] ![(1/6400),1,(1/4)] 29061008056983261357650477056000000000 25875116435593143473457239891329941504 513264682944005437120315392000000000000 raw00293 affine00293
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00293_raw leaf00293_rectangular
    leaf00293_transform leaf00293_sign leaf00293_log
#print axioms leaf00293_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
