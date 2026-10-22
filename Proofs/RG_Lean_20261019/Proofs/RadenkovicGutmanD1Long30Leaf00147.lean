/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00147 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4872376317637961431453270016000000000000 4333044992696506168432377289593738756096 85441894379555107186292031488000000000000))
theorem leaf00147_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4872376317637961431453270016000000000000 4333044992696506168432377289593738756096 85441894379555107186292031488000000000000 raw00147=true := by decide +kernel
#print axioms leaf00147_raw
theorem leaf00147_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00147=true := by decide +kernel
#print axioms leaf00147_rectangular
def affine00147 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00147 (IntegerComputedClassCell.leftNumerator ![(103/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(103/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(103/32000),0,(1/8)] ![(3/32000),1,(1/8)]))
theorem leaf00147_transform : affine00147=(NestedInteger.clearedAll 3 raw00147 (IntegerComputedClassCell.leftNumerator ![(103/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(103/32000),0,(1/8)] ![(3/32000),1,(1/8)]) (IntegerComputedClassCell.denominator ![(103/32000),0,(1/8)] ![(3/32000),1,(1/8)])) := by decide +kernel
#print axioms leaf00147_transform
theorem leaf00147_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00147=true := by decide +kernel
#print axioms leaf00147_sign
theorem leaf00147_log : RationalLog.accepts (1817598639/2147483648) (-11192455/134217728) 1 8=true := by decide +kernel
#print axioms leaf00147_log
def leaf00147 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (12678338373/250000000000) (1817598639/2147483648) (-11192455/134217728) 1 8 ![60,0,4] ![(103/32000),0,(1/8)] ![(3/32000),1,(1/8)] affine00147
theorem leaf00147_checked : FastNestedCellData.accepts 1 2 4 leaf00147=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (12678338373/250000000000) (1817598639/2147483648) (-11192455/134217728) 1 8 ![60,0,4] ![(103/32000),0,(1/8)] ![(3/32000),1,(1/8)] 4872376317637961431453270016000000000000 4333044992696506168432377289593738756096 85441894379555107186292031488000000000000 raw00147 affine00147
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00147_raw leaf00147_rectangular
    leaf00147_transform leaf00147_sign leaf00147_log
#print axioms leaf00147_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
