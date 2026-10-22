/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00251 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 768097635366188135877554733056000000000000 527638164446038214298422198534733954023424 3167958647085817997647115452416000000000000))
theorem leaf00251_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 768097635366188135877554733056000000000000 527638164446038214298422198534733954023424 3167958647085817997647115452416000000000000 raw00251=true := by decide +kernel
#print axioms leaf00251_raw
theorem leaf00251_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00251=true := by decide +kernel
#print axioms leaf00251_rectangular
def affine00251 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00251 (IntegerComputedClassCell.leftNumerator ![(17/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/3200),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00251_transform : affine00251=(NestedInteger.clearedAll 3 raw00251 (IntegerComputedClassCell.leftNumerator ![(17/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/3200),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00251_transform
theorem leaf00251_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00251=true := by decide +kernel
#print axioms leaf00251_sign
theorem leaf00251_log : RationalLog.accepts (1264574903/2147483648) (-1137223065/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00251_log
def leaf00251 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (166554624989/1000000000000) (1264574903/2147483648) (-1137223065/4294967296) 1 8 ![60,0,4] ![(17/3200),0,(1/16)] ![(1/6400),1,(1/16)] affine00251
theorem leaf00251_checked : FastNestedCellData.accepts 1 2 4 leaf00251=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (166554624989/1000000000000) (1264574903/2147483648) (-1137223065/4294967296) 1 8 ![60,0,4] ![(17/3200),0,(1/16)] ![(1/6400),1,(1/16)] 768097635366188135877554733056000000000000 527638164446038214298422198534733954023424 3167958647085817997647115452416000000000000 raw00251 affine00251
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00251_raw leaf00251_rectangular
    leaf00251_transform leaf00251_sign leaf00251_log
#print axioms leaf00251_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
