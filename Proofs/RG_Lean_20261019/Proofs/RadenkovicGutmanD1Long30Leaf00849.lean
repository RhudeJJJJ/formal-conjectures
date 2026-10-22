/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00849 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 131320648640282601101824779878400000000000 93248757655274801203655348600708611964928 523949884643066564312866540748800000000000))
theorem leaf00849_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 131320648640282601101824779878400000000000 93248757655274801203655348600708611964928 523949884643066564312866540748800000000000 raw00849=true := by decide +kernel
#print axioms leaf00849_raw
theorem leaf00849_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00849=true := by decide +kernel
#print axioms leaf00849_rectangular
def affine00849 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00849 (IntegerComputedClassCell.leftNumerator ![(33/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(33/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(33/640),0,(1/2)] ![(1/640),1,(1/2)]))
theorem leaf00849_transform : affine00849=(NestedInteger.clearedAll 3 raw00849 (IntegerComputedClassCell.leftNumerator ![(33/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(33/640),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(33/640),0,(1/2)] ![(1/640),1,(1/2)])) := by decide +kernel
#print axioms leaf00849_transform
theorem leaf00849_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00849=true := by decide +kernel
#print axioms leaf00849_sign
theorem leaf00849_log : RationalLog.accepts (2589015697/4294967296) (-1086983625/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00849_log
def leaf00849 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (35594533137/200000000000) (2589015697/4294967296) (-1086983625/4294967296) 1 8 ![60,0,4] ![(33/640),0,(1/2)] ![(1/640),1,(1/2)] affine00849
theorem leaf00849_checked : FastNestedCellData.accepts 1 2 4 leaf00849=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (35594533137/200000000000) (2589015697/4294967296) (-1086983625/4294967296) 1 8 ![60,0,4] ![(33/640),0,(1/2)] ![(1/640),1,(1/2)] 131320648640282601101824779878400000000000 93248757655274801203655348600708611964928 523949884643066564312866540748800000000000 raw00849 affine00849
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00849_raw leaf00849_rectangular
    leaf00849_transform leaf00849_sign leaf00849_log
#print axioms leaf00849_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
