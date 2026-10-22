/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01336 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 288621846036914980463312896000000000000 292008138202698759317947905972222558208 1166448301391018578095319810048000000000000))
theorem leaf01336_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 288621846036914980463312896000000000000 292008138202698759317947905972222558208 1166448301391018578095319810048000000000000 raw01336=true := by decide +kernel
#print axioms leaf01336_raw
theorem leaf01336_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01336=true := by decide +kernel
#print axioms leaf01336_rectangular
def affine01336 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01336 (IntegerComputedClassCell.leftNumerator ![(5/64),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(5/64),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(5/64),0,0] ![(1/256),1,1]))
theorem leaf01336_transform : affine01336=(NestedInteger.clearedAll 3 raw01336 (IntegerComputedClassCell.leftNumerator ![(5/64),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.widthNumerator ![(5/64),0,0] ![(1/256),1,1]) (IntegerComputedClassCell.denominator ![(5/64),0,0] ![(1/256),1,1])) := by decide +kernel
#print axioms leaf01336_transform
theorem leaf01336_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01336=true := by decide +kernel
#print axioms leaf01336_sign
theorem leaf01336_log : RationalLog.accepts (2172135499/2147483648) (12255715/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01336_log
def leaf01336 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (125169773/500000000000) (2172135499/2147483648) (12255715/2147483648) 0 8 ![60,0,4] ![(5/64),0,0] ![(1/256),1,1] affine01336
theorem leaf01336_checked : FastNestedCellData.accepts 1 2 4 leaf01336=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (125169773/500000000000) (2172135499/2147483648) (12255715/2147483648) 0 8 ![60,0,4] ![(5/64),0,0] ![(1/256),1,1] 288621846036914980463312896000000000000 292008138202698759317947905972222558208 1166448301391018578095319810048000000000000 raw01336 affine01336
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01336_raw leaf01336_rectangular
    leaf01336_transform leaf01336_sign leaf01336_log
#print axioms leaf01336_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
