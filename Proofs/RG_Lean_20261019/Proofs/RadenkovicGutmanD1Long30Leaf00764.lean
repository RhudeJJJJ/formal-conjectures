/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00764 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2323365677681003263720765259776000000000000 1786443268461978458143713294674686096965632 14183760263004064179307006656512000000000000))
theorem leaf00764_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2323365677681003263720765259776000000000000 1786443268461978458143713294674686096965632 14183760263004064179307006656512000000000000 raw00764=true := by decide +kernel
#print axioms leaf00764_raw
theorem leaf00764_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00764=true := by decide +kernel
#print axioms leaf00764_rectangular
def affine00764 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00764 (IntegerComputedClassCell.leftNumerator ![(7/200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/200),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00764_transform : affine00764=(NestedInteger.clearedAll 3 raw00764 (IntegerComputedClassCell.leftNumerator ![(7/200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/200),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00764_transform
theorem leaf00764_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00764=true := by decide +kernel
#print axioms leaf00764_sign
theorem leaf00764_log : RationalLog.accepts (2933002627/4294967296) (-819087355/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00764_log
def leaf00764 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (125949905761/1000000000000) (2933002627/4294967296) (-819087355/4294967296) 1 8 ![60,0,4] ![(7/200),0,(1/2)] ![(3/3200),1,(1/2)] affine00764
theorem leaf00764_checked : FastNestedCellData.accepts 1 2 4 leaf00764=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (125949905761/1000000000000) (2933002627/4294967296) (-819087355/4294967296) 1 8 ![60,0,4] ![(7/200),0,(1/2)] ![(3/3200),1,(1/2)] 2323365677681003263720765259776000000000000 1786443268461978458143713294674686096965632 14183760263004064179307006656512000000000000 raw00764 affine00764
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00764_raw leaf00764_rectangular
    leaf00764_transform leaf00764_sign leaf00764_log
#print axioms leaf00764_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
