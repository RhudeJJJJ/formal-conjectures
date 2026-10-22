/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01067 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 322605598927331379008850257510400000000000 320244224093217467906838564142902354640896 915585975967819507338882056192000000000000))
theorem leaf01067_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 322605598927331379008850257510400000000000 320244224093217467906838564142902354640896 915585975967819507338882056192000000000000 raw01067=true := by decide +kernel
#print axioms leaf01067_raw
theorem leaf01067_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01067=true := by decide +kernel
#print axioms leaf01067_rectangular
def affine01067 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01067 (IntegerComputedClassCell.leftNumerator ![(53/160),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(53/160),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(53/160),0,(1/8)] ![(3/160),1,(1/8)]))
theorem leaf01067_transform : affine01067=(NestedInteger.clearedAll 3 raw01067 (IntegerComputedClassCell.leftNumerator ![(53/160),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(53/160),0,(1/8)] ![(3/160),1,(1/8)]) (IntegerComputedClassCell.denominator ![(53/160),0,(1/8)] ![(3/160),1,(1/8)])) := by decide +kernel
#print axioms leaf01067_transform
theorem leaf01067_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01067=true := by decide +kernel
#print axioms leaf01067_sign
theorem leaf01067_log : RationalLog.accepts (1579354415/2147483648) (-659880089/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01067_log
def leaf01067 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (349769691213/1000000000000) (1579354415/2147483648) (-659880089/4294967296) 1 8 ![60,0,4] ![(53/160),0,(1/8)] ![(3/160),1,(1/8)] affine01067
theorem leaf01067_checked : FastNestedCellData.accepts 1 2 4 leaf01067=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (349769691213/1000000000000) (1579354415/2147483648) (-659880089/4294967296) 1 8 ![60,0,4] ![(53/160),0,(1/8)] ![(3/160),1,(1/8)] 322605598927331379008850257510400000000000 320244224093217467906838564142902354640896 915585975967819507338882056192000000000000 raw01067 affine01067
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01067_raw leaf01067_rectangular
    leaf01067_transform leaf01067_sign leaf01067_log
#print axioms leaf01067_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
