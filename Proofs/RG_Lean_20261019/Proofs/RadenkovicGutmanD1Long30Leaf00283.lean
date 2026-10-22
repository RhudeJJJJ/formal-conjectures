/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00283 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 221620814726980745968941531136000000000000 198345527357285303499395140721005073268736 4127352823145454061651234914304000000000000))
theorem leaf00283_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 221620814726980745968941531136000000000000 198345527357285303499395140721005073268736 4127352823145454061651234914304000000000000 raw00283=true := by decide +kernel
#print axioms leaf00283_raw
theorem leaf00283_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00283=true := by decide +kernel
#print axioms leaf00283_rectangular
def affine00283 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00283 (IntegerComputedClassCell.leftNumerator ![(1/160),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/160),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/160),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00283_transform : affine00283=(NestedInteger.clearedAll 3 raw00283 (IntegerComputedClassCell.leftNumerator ![(1/160),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(1/160),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(1/160),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00283_transform
theorem leaf00283_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00283=true := by decide +kernel
#print axioms leaf00283_sign
theorem leaf00283_log : RationalLog.accepts (1833821647/2147483648) (-10596131/134217728) 1 8=true := by decide +kernel
#print axioms leaf00283_log
def leaf00283 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (48056353759/1000000000000) (1833821647/2147483648) (-10596131/134217728) 1 8 ![60,0,4] ![(1/160),0,(1/4)] ![(1/6400),1,(1/4)] affine00283
theorem leaf00283_checked : FastNestedCellData.accepts 1 2 4 leaf00283=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (48056353759/1000000000000) (1833821647/2147483648) (-10596131/134217728) 1 8 ![60,0,4] ![(1/160),0,(1/4)] ![(1/6400),1,(1/4)] 221620814726980745968941531136000000000000 198345527357285303499395140721005073268736 4127352823145454061651234914304000000000000 raw00283 affine00283
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00283_raw leaf00283_rectangular
    leaf00283_transform leaf00283_sign leaf00283_log
#print axioms leaf00283_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
