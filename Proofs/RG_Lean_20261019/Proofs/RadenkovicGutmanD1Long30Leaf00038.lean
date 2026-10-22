/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00038 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 10319563866350385789361612390400000000000 10046437971117285625340972218180108812288 897925883815185211930838040576000000000000))
theorem leaf00038_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 10319563866350385789361612390400000000000 10046437971117285625340972218180108812288 897925883815185211930838040576000000000000 raw00038=true := by decide +kernel
#print axioms leaf00038_raw
theorem leaf00038_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00038=true := by decide +kernel
#print axioms leaf00038_rectangular
def affine00038 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00038 (IntegerComputedClassCell.leftNumerator ![(23/16000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/16000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/16000),0,(1/4)] ![(1/16000),1,(1/4)]))
theorem leaf00038_transform : affine00038=(NestedInteger.clearedAll 3 raw00038 (IntegerComputedClassCell.leftNumerator ![(23/16000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/16000),0,(1/4)] ![(1/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/16000),0,(1/4)] ![(1/16000),1,(1/4)])) := by decide +kernel
#print axioms leaf00038_transform
theorem leaf00038_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00038=true := by decide +kernel
#print axioms leaf00038_sign
theorem leaf00038_log : RationalLog.accepts (2067514245/2147483648) (-81496445/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00038_log
def leaf00038 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (11188493563/1000000000000) (2067514245/2147483648) (-81496445/4294967296) 1 8 ![60,0,4] ![(23/16000),0,(1/4)] ![(1/16000),1,(1/4)] affine00038
theorem leaf00038_checked : FastNestedCellData.accepts 1 2 4 leaf00038=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (11188493563/1000000000000) (2067514245/2147483648) (-81496445/4294967296) 1 8 ![60,0,4] ![(23/16000),0,(1/4)] ![(1/16000),1,(1/4)] 10319563866350385789361612390400000000000 10046437971117285625340972218180108812288 897925883815185211930838040576000000000000 raw00038 affine00038
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00038_raw leaf00038_rectangular
    leaf00038_transform leaf00038_sign leaf00038_log
#print axioms leaf00038_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
