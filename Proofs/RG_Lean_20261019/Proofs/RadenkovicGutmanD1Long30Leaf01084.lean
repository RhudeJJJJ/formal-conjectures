/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01084 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 308811463481435144374007627776000000000000 321582424169826040092413179722777554321408 1200600807201841753695356715008000000000000))
theorem leaf01084_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 308811463481435144374007627776000000000000 321582424169826040092413179722777554321408 1200600807201841753695356715008000000000000 raw01084=true := by decide +kernel
#print axioms leaf01084_raw
theorem leaf01084_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01084=true := by decide +kernel
#print axioms leaf01084_rectangular
def affine01084 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01084 (IntegerComputedClassCell.leftNumerator ![(31/80),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(31/80),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(31/80),0,(1/2)] ![(3/80),1,(1/2)]))
theorem leaf01084_transform : affine01084=(NestedInteger.clearedAll 3 raw01084 (IntegerComputedClassCell.leftNumerator ![(31/80),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(31/80),0,(1/2)] ![(3/80),1,(1/2)]) (IntegerComputedClassCell.denominator ![(31/80),0,(1/2)] ![(3/80),1,(1/2)])) := by decide +kernel
#print axioms leaf01084_transform
theorem leaf01084_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01084=true := by decide +kernel
#print axioms leaf01084_sign
theorem leaf01084_log : RationalLog.accepts (3527690293/4294967296) (-422626089/4294967296) 1 8=true := by decide +kernel
#print axioms leaf01084_log
def leaf01084 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (66962811919/250000000000) (3527690293/4294967296) (-422626089/4294967296) 1 8 ![60,0,4] ![(31/80),0,(1/2)] ![(3/80),1,(1/2)] affine01084
theorem leaf01084_checked : FastNestedCellData.accepts 1 2 4 leaf01084=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (66962811919/250000000000) (3527690293/4294967296) (-422626089/4294967296) 1 8 ![60,0,4] ![(31/80),0,(1/2)] ![(3/80),1,(1/2)] 308811463481435144374007627776000000000000 321582424169826040092413179722777554321408 1200600807201841753695356715008000000000000 raw01084 affine01084
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01084_raw leaf01084_rectangular
    leaf01084_transform leaf01084_sign leaf01084_log
#print axioms leaf01084_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
