/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00423 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 124191886925775581484247154688000000000000 103597866462409042240946797419790816247808 1282318955851325764016996876288000000000000))
theorem leaf00423_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 124191886925775581484247154688000000000000 103597866462409042240946797419790816247808 1282318955851325764016996876288000000000000 raw00423=true := by decide +kernel
#print axioms leaf00423_raw
theorem leaf00423_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00423=true := by decide +kernel
#print axioms leaf00423_rectangular
def affine00423 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00423 (IntegerComputedClassCell.leftNumerator ![(17/1600),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/1600),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/1600),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00423_transform : affine00423=(NestedInteger.clearedAll 3 raw00423 (IntegerComputedClassCell.leftNumerator ![(17/1600),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(17/1600),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(17/1600),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00423_transform
theorem leaf00423_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00423=true := by decide +kernel
#print axioms leaf00423_sign
theorem leaf00423_log : RationalLog.accepts (3314945121/4294967296) (-556204469/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00423_log
def leaf00423 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (40394734083/500000000000) (3314945121/4294967296) (-556204469/4294967296) 1 8 ![60,0,4] ![(17/1600),0,(1/4)] ![(1/6400),1,(1/4)] affine00423
theorem leaf00423_checked : FastNestedCellData.accepts 1 2 4 leaf00423=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (40394734083/500000000000) (3314945121/4294967296) (-556204469/4294967296) 1 8 ![60,0,4] ![(17/1600),0,(1/4)] ![(1/6400),1,(1/4)] 124191886925775581484247154688000000000000 103597866462409042240946797419790816247808 1282318955851325764016996876288000000000000 raw00423 affine00423
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00423_raw leaf00423_rectangular
    leaf00423_transform leaf00423_sign leaf00423_log
#print axioms leaf00423_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
