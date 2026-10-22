/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00839 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 125287916666498027390835150028800000000000 90153682417050274435910974219480939364352 530950454312889806258989275545600000000000))
theorem leaf00839_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 125287916666498027390835150028800000000000 90153682417050274435910974219480939364352 530950454312889806258989275545600000000000 raw00839=true := by decide +kernel
#print axioms leaf00839_raw
theorem leaf00839_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00839=true := by decide +kernel
#print axioms leaf00839_rectangular
def affine00839 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00839 (IntegerComputedClassCell.leftNumerator ![(157/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(157/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(157/3200),0,(1/2)] ![(3/3200),1,(1/2)]))
theorem leaf00839_transform : affine00839=(NestedInteger.clearedAll 3 raw00839 (IntegerComputedClassCell.leftNumerator ![(157/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(157/3200),0,(1/2)] ![(3/3200),1,(1/2)]) (IntegerComputedClassCell.denominator ![(157/3200),0,(1/2)] ![(3/3200),1,(1/2)])) := by decide +kernel
#print axioms leaf00839_transform
theorem leaf00839_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00839=true := by decide +kernel
#print axioms leaf00839_sign
theorem leaf00839_log : RationalLog.accepts (2641944677/4294967296) (-1043523919/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00839_log
def leaf00839 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (33959357859/200000000000) (2641944677/4294967296) (-1043523919/4294967296) 1 8 ![60,0,4] ![(157/3200),0,(1/2)] ![(3/3200),1,(1/2)] affine00839
theorem leaf00839_checked : FastNestedCellData.accepts 1 2 4 leaf00839=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (33959357859/200000000000) (2641944677/4294967296) (-1043523919/4294967296) 1 8 ![60,0,4] ![(157/3200),0,(1/2)] ![(3/3200),1,(1/2)] 125287916666498027390835150028800000000000 90153682417050274435910974219480939364352 530950454312889806258989275545600000000000 raw00839 affine00839
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00839_raw leaf00839_rectangular
    leaf00839_transform leaf00839_sign leaf00839_log
#print axioms leaf00839_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
