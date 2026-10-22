/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00734 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 32940403271376482866659590144000000000000 25908890072870681266560358008966220873728 226704241288567936070795132928000000000000))
theorem leaf00734_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 32940403271376482866659590144000000000000 25908890072870681266560358008966220873728 226704241288567936070795132928000000000000 raw00734=true := by decide +kernel
#print axioms leaf00734_raw
theorem leaf00734_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00734=true := by decide +kernel
#print axioms leaf00734_rectangular
def affine00734 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00734 (IntegerComputedClassCell.leftNumerator ![(203/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(203/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(203/6400),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00734_transform : affine00734=(NestedInteger.clearedAll 3 raw00734 (IntegerComputedClassCell.leftNumerator ![(203/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(203/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(203/6400),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00734_transform
theorem leaf00734_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00734=true := by decide +kernel
#print axioms leaf00734_sign
theorem leaf00734_log : RationalLog.accepts (757920213/1073741824) (-748026011/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00734_log
def leaf00734 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (57142490863/500000000000) (757920213/1073741824) (-748026011/4294967296) 1 8 ![60,0,4] ![(203/6400),0,(1/2)] ![(3/6400),1,(1/2)] affine00734
theorem leaf00734_checked : FastNestedCellData.accepts 1 2 4 leaf00734=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (57142490863/500000000000) (757920213/1073741824) (-748026011/4294967296) 1 8 ![60,0,4] ![(203/6400),0,(1/2)] ![(3/6400),1,(1/2)] 32940403271376482866659590144000000000000 25908890072870681266560358008966220873728 226704241288567936070795132928000000000000 raw00734 affine00734
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00734_raw leaf00734_rectangular
    leaf00734_transform leaf00734_sign leaf00734_log
#print axioms leaf00734_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
