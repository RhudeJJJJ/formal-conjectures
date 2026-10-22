/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01082 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1378106934027543133342119493632000000000000 1457468699660914552268892396321080296341504 4877261596005764243547213529088000000000000))
theorem leaf01082_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1378106934027543133342119493632000000000000 1457468699660914552268892396321080296341504 4877261596005764243547213529088000000000000 raw01082=true := by decide +kernel
#print axioms leaf01082_raw
theorem leaf01082_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01082=true := by decide +kernel
#print axioms leaf01082_rectangular
def affine01082 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01082 (IntegerComputedClassCell.leftNumerator ![(31/80),0,(1/8)] ![(3/80),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(31/80),0,(1/8)] ![(3/80),1,(1/8)]) (IntegerComputedClassCell.denominator ![(31/80),0,(1/8)] ![(3/80),1,(1/8)]))
theorem leaf01082_transform : affine01082=(NestedInteger.clearedAll 3 raw01082 (IntegerComputedClassCell.leftNumerator ![(31/80),0,(1/8)] ![(3/80),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(31/80),0,(1/8)] ![(3/80),1,(1/8)]) (IntegerComputedClassCell.denominator ![(31/80),0,(1/8)] ![(3/80),1,(1/8)])) := by decide +kernel
#print axioms leaf01082_transform
theorem leaf01082_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01082=true := by decide +kernel
#print axioms leaf01082_sign
theorem leaf01082_log : RationalLog.accepts (3497229239/4294967296) (-441249797/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01082_log
def leaf01082 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (149414653179/500000000000) (3497229239/4294967296) (-441249797/4294967296) 1 8 ![60,0,4] ![(31/80),0,(1/8)] ![(3/80),1,(1/8)] affine01082
theorem leaf01082_checked : FastNestedCellData.accepts 1 2 4 leaf01082=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (149414653179/500000000000) (3497229239/4294967296) (-441249797/4294967296) 1 8 ![60,0,4] ![(31/80),0,(1/8)] ![(3/80),1,(1/8)] 1378106934027543133342119493632000000000000 1457468699660914552268892396321080296341504 4877261596005764243547213529088000000000000 raw01082 affine01082
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01082_raw leaf01082_rectangular
    leaf01082_transform leaf01082_sign leaf01082_log
#print axioms leaf01082_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
