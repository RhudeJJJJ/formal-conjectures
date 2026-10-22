/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00451 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 61932298996474980525067678515200000000000 29820654215345723939530601502659032645632 88821824045701962084778613145600000000000))
theorem leaf00451_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 61932298996474980525067678515200000000000 29820654215345723939530601502659032645632 88821824045701962084778613145600000000000 raw00451=true := by decide +kernel
#print axioms leaf00451_raw
theorem leaf00451_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00451=true := by decide +kernel
#print axioms leaf00451_rectangular
def affine00451 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00451 (IntegerComputedClassCell.leftNumerator ![(37/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(37/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(37/3200),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00451_transform : affine00451=(NestedInteger.clearedAll 3 raw00451 (IntegerComputedClassCell.leftNumerator ![(37/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(37/3200),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(37/3200),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00451_transform
theorem leaf00451_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00451=true := by decide +kernel
#print axioms leaf00451_sign
theorem leaf00451_log : RationalLog.accepts (774121819/2147483648) (-2191126577/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00451_log
def leaf00451 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (67147133119/200000000000) (774121819/2147483648) (-2191126577/4294967296) 2 8 ![60,0,4] ![(37/3200),0,(1/16)] ![(1/6400),1,(1/16)] affine00451
theorem leaf00451_checked : FastNestedCellData.accepts 1 2 4 leaf00451=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (67147133119/200000000000) (774121819/2147483648) (-2191126577/4294967296) 2 8 ![60,0,4] ![(37/3200),0,(1/16)] ![(1/6400),1,(1/16)] 61932298996474980525067678515200000000000 29820654215345723939530601502659032645632 88821824045701962084778613145600000000000 raw00451 affine00451
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00451_raw leaf00451_rectangular
    leaf00451_transform leaf00451_sign leaf00451_log
#print axioms leaf00451_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
