/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00630 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3918753894368169194647472570368000000000000 72083697215725786685982579942240349585408 84829868771311030429259137024000000000000))
theorem leaf00630_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3918753894368169194647472570368000000000000 72083697215725786685982579942240349585408 84829868771311030429259137024000000000000 raw00630=true := by decide +kernel
#print axioms leaf00630_raw
theorem leaf00630_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00630=true := by decide +kernel
#print axioms leaf00630_rectangular
def affine00630 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00630 (IntegerComputedClassCell.leftNumerator ![(143/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(143/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(143/6400),0,0] ![(3/6400),1,(1/16)]))
theorem leaf00630_transform : affine00630=(NestedInteger.clearedAll 3 raw00630 (IntegerComputedClassCell.leftNumerator ![(143/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(143/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(143/6400),0,0] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00630_transform
theorem leaf00630_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00630=true := by decide +kernel
#print axioms leaf00630_sign
theorem leaf00630_log : RationalLog.accepts (42710753/4294967296) (-4950753633/2147483648) 7 8=true := by decide +kernel
#print axioms leaf00630_log
def leaf00630 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (424872148571/500000000000) (42710753/4294967296) (-4950753633/2147483648) 7 8 ![60,0,4] ![(143/6400),0,0] ![(3/6400),1,(1/16)] affine00630
theorem leaf00630_checked : FastNestedCellData.accepts 1 2 4 leaf00630=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (424872148571/500000000000) (42710753/4294967296) (-4950753633/2147483648) 7 8 ![60,0,4] ![(143/6400),0,0] ![(3/6400),1,(1/16)] 3918753894368169194647472570368000000000000 72083697215725786685982579942240349585408 84829868771311030429259137024000000000000 raw00630 affine00630
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00630_raw leaf00630_rectangular
    leaf00630_transform leaf00630_sign leaf00630_log
#print axioms leaf00630_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
