/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00535 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3647922691321556731254162849792000000000000 31713311519848429740398816922906705002496 40091813261846734193821745152000000000000))
theorem leaf00535_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3647922691321556731254162849792000000000000 31713311519848429740398816922906705002496 40091813261846734193821745152000000000000 raw00535=true := by decide +kernel
#print axioms leaf00535_raw
theorem leaf00535_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00535=true := by decide +kernel
#print axioms leaf00535_rectangular
def affine00535 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00535 (IntegerComputedClassCell.leftNumerator ![(1/64),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/64),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/64),0,0] ![(1/3200),1,(1/16)]))
theorem leaf00535_transform : affine00535=(NestedInteger.clearedAll 3 raw00535 (IntegerComputedClassCell.leftNumerator ![(1/64),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/64),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/64),0,0] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00535_transform
theorem leaf00535_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00535=true := by decide +kernel
#print axioms leaf00535_sign
theorem leaf00535_log : RationalLog.accepts (20847601/4294967296) (-5720853993/2147483648) 8 8=true := by decide +kernel
#print axioms leaf00535_log
def leaf00535 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (395508570699/500000000000) (20847601/4294967296) (-5720853993/2147483648) 8 8 ![60,0,4] ![(1/64),0,0] ![(1/3200),1,(1/16)] affine00535
theorem leaf00535_checked : FastNestedCellData.accepts 1 2 4 leaf00535=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (395508570699/500000000000) (20847601/4294967296) (-5720853993/2147483648) 8 8 ![60,0,4] ![(1/64),0,0] ![(1/3200),1,(1/16)] 3647922691321556731254162849792000000000000 31713311519848429740398816922906705002496 40091813261846734193821745152000000000000 raw00535 affine00535
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00535_raw leaf00535_rectangular
    leaf00535_transform leaf00535_sign leaf00535_log
#print axioms leaf00535_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
