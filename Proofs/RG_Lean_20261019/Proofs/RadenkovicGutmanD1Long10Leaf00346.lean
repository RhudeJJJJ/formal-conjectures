/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00346 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2292830764253274801156124573696000000000000 1403192931155176511657718473274734480982016 2822312628848542056205552451584000000000000))
theorem leaf00346_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2292830764253274801156124573696000000000000 1403192931155176511657718473274734480982016 2822312628848542056205552451584000000000000 raw00346=true := by decide +kernel
#print axioms leaf00346_raw
theorem leaf00346_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00346=true := by decide +kernel
#print axioms leaf00346_rectangular
def affine00346 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00346 (IntegerComputedClassCell.leftNumerator ![(3/20),0,(1/4)] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/20),0,(1/4)] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/20),0,(1/4)] ![(1/80),1,(1/4)]))
theorem leaf00346_transform : affine00346=(NestedInteger.clearedAll 3 raw00346 (IntegerComputedClassCell.leftNumerator ![(3/20),0,(1/4)] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/20),0,(1/4)] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/20),0,(1/4)] ![(1/80),1,(1/4)])) := by decide +kernel
#print axioms leaf00346_transform
theorem leaf00346_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00346=true := by decide +kernel
#print axioms leaf00346_sign
theorem leaf00346_log : RationalLog.accepts (877812367/2147483648) (-960590059/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00346_log
def leaf00346 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (497178419149/1000000000000) (877812367/2147483648) (-960590059/2147483648) 2 8 ![52,0,4] ![(3/20),0,(1/4)] ![(1/80),1,(1/4)] affine00346
theorem leaf00346_checked : FastNestedCellData.accepts 1 0 4 leaf00346=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (497178419149/1000000000000) (877812367/2147483648) (-960590059/2147483648) 2 8 ![52,0,4] ![(3/20),0,(1/4)] ![(1/80),1,(1/4)] 2292830764253274801156124573696000000000000 1403192931155176511657718473274734480982016 2822312628848542056205552451584000000000000 raw00346 affine00346
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00346_raw leaf00346_rectangular
    leaf00346_transform leaf00346_sign leaf00346_log
#print axioms leaf00346_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
