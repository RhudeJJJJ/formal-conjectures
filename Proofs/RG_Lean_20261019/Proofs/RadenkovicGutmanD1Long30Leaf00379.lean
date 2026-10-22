/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00379 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 39467589679933153842460360704000000000000 36471252992810203325501333297939582287872 1065392951947779746434927034368000000000000))
theorem leaf00379_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 39467589679933153842460360704000000000000 36471252992810203325501333297939582287872 1065392951947779746434927034368000000000000 raw00379=true := by decide +kernel
#print axioms leaf00379_raw
theorem leaf00379_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00379=true := by decide +kernel
#print axioms leaf00379_rectangular
def affine00379 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00379 (IntegerComputedClassCell.leftNumerator ![(59/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(59/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(59/6400),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00379_transform : affine00379=(NestedInteger.clearedAll 3 raw00379 (IntegerComputedClassCell.leftNumerator ![(59/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(59/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(59/6400),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00379_transform
theorem leaf00379_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00379=true := by decide +kernel
#print axioms leaf00379_sign
theorem leaf00379_log : RationalLog.accepts (959382283/1073741824) (-241839415/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00379_log
def leaf00379 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (34232677179/1000000000000) (959382283/1073741824) (-241839415/4294967296) 1 8 ![60,0,4] ![(59/6400),0,(1/2)] ![(1/6400),1,(1/2)] affine00379
theorem leaf00379_checked : FastNestedCellData.accepts 1 2 4 leaf00379=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (34232677179/1000000000000) (959382283/1073741824) (-241839415/4294967296) 1 8 ![60,0,4] ![(59/6400),0,(1/2)] ![(1/6400),1,(1/2)] 39467589679933153842460360704000000000000 36471252992810203325501333297939582287872 1065392951947779746434927034368000000000000 raw00379 affine00379
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00379_raw leaf00379_rectangular
    leaf00379_transform leaf00379_sign leaf00379_log
#print axioms leaf00379_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
