/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01352 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 310225740559007132680192000000000000 310461110645466148666620074788913152 72112264556590167455344623616000000000000))
theorem leaf01352_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 310225740559007132680192000000000000 310461110645466148666620074788913152 72112264556590167455344623616000000000000 raw01352=true := by decide +kernel
#print axioms leaf01352_raw
theorem leaf01352_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01352=true := by decide +kernel
#print axioms leaf01352_rectangular
def affine01352 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01352 (IntegerComputedClassCell.leftNumerator ![(5/256),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.widthNumerator ![(5/256),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.denominator ![(5/256),0,0] ![(1/512),1,1]))
theorem leaf01352_transform : affine01352=(NestedInteger.clearedAll 3 raw01352 (IntegerComputedClassCell.leftNumerator ![(5/256),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.widthNumerator ![(5/256),0,0] ![(1/512),1,1]) (IntegerComputedClassCell.denominator ![(5/256),0,0] ![(1/512),1,1])) := by decide +kernel
#print axioms leaf01352_transform
theorem leaf01352_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01352=true := by decide +kernel
#print axioms leaf01352_sign
theorem leaf01352_log : RationalLog.accepts (268637963/268435456) (1619445/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01352_log
def leaf01352 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (4305247/1000000000000) (268637963/268435456) (1619445/4294967296) 0 8 ![60,0,4] ![(5/256),0,0] ![(1/512),1,1] affine01352
theorem leaf01352_checked : FastNestedCellData.accepts 1 2 4 leaf01352=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (4305247/1000000000000) (268637963/268435456) (1619445/4294967296) 0 8 ![60,0,4] ![(5/256),0,0] ![(1/512),1,1] 310225740559007132680192000000000000 310461110645466148666620074788913152 72112264556590167455344623616000000000000 raw01352 affine01352
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01352_raw leaf01352_rectangular
    leaf01352_transform leaf01352_sign leaf01352_log
#print axioms leaf01352_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
