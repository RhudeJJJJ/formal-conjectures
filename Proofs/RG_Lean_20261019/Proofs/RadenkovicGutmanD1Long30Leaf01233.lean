/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01233 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 29126828775490403168942869708800000000000 32199000686925649730066086462854537412608 4078485369479877405379250880512000000000000))
theorem leaf01233_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 29126828775490403168942869708800000000000 32199000686925649730066086462854537412608 4078485369479877405379250880512000000000000 raw01233=true := by decide +kernel
#print axioms leaf01233_raw
theorem leaf01233_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01233=true := by decide +kernel
#print axioms leaf01233_rectangular
def affine01233 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01233 (IntegerComputedClassCell.leftNumerator ![(17/64),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/64),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/64),0,(7/8)] ![(1/64),1,(1/16)]))
theorem leaf01233_transform : affine01233=(NestedInteger.clearedAll 3 raw01233 (IntegerComputedClassCell.leftNumerator ![(17/64),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(17/64),0,(7/8)] ![(1/64),1,(1/16)]) (IntegerComputedClassCell.denominator ![(17/64),0,(7/8)] ![(1/64),1,(1/16)])) := by decide +kernel
#print axioms leaf01233_transform
theorem leaf01233_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01233=true := by decide +kernel
#print axioms leaf01233_sign
theorem leaf01233_log : RationalLog.accepts (4710790915/4294967296) (198452991/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01233_log
def leaf01233 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (7894842759/1000000000000) (4710790915/4294967296) (198452991/4294967296) 0 8 ![60,0,4] ![(17/64),0,(7/8)] ![(1/64),1,(1/16)] affine01233
theorem leaf01233_checked : FastNestedCellData.accepts 1 2 4 leaf01233=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (7894842759/1000000000000) (4710790915/4294967296) (198452991/4294967296) 0 8 ![60,0,4] ![(17/64),0,(7/8)] ![(1/64),1,(1/16)] 29126828775490403168942869708800000000000 32199000686925649730066086462854537412608 4078485369479877405379250880512000000000000 raw01233 affine01233
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01233_raw leaf01233_rectangular
    leaf01233_transform leaf01233_sign leaf01233_log
#print axioms leaf01233_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
