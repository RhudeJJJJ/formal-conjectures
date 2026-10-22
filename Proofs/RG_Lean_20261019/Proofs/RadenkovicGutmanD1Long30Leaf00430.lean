/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00430 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3216544036150808973170507251712000000000000 12779679724550023579708321840602537787392 18322730745578414772232126464000000000000))
theorem leaf00430_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3216544036150808973170507251712000000000000 12779679724550023579708321840602537787392 18322730745578414772232126464000000000000 raw00430=true := by decide +kernel
#print axioms leaf00430_raw
theorem leaf00430_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00430=true := by decide +kernel
#print axioms leaf00430_rectangular
def affine00430 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00430 (IntegerComputedClassCell.leftNumerator ![(7/640),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/640),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/640),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00430_transform : affine00430=(NestedInteger.clearedAll 3 raw00430 (IntegerComputedClassCell.leftNumerator ![(7/640),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/640),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/640),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00430_transform
theorem leaf00430_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00430=true := by decide +kernel
#print axioms leaf00430_sign
theorem leaf00430_log : RationalLog.accepts (10052787/4294967296) (-406501841/134217728) 9 8=true := by decide +kernel
#print axioms leaf00430_log
def leaf00430 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (348738403189/500000000000) (10052787/4294967296) (-406501841/134217728) 9 8 ![60,0,4] ![(7/640),0,0] ![(1/6400),1,(1/16)] affine00430
theorem leaf00430_checked : FastNestedCellData.accepts 1 2 4 leaf00430=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (348738403189/500000000000) (10052787/4294967296) (-406501841/134217728) 9 8 ![60,0,4] ![(7/640),0,0] ![(1/6400),1,(1/16)] 3216544036150808973170507251712000000000000 12779679724550023579708321840602537787392 18322730745578414772232126464000000000000 raw00430 affine00430
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00430_raw leaf00430_rectangular
    leaf00430_transform leaf00430_sign leaf00430_log
#print axioms leaf00430_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
