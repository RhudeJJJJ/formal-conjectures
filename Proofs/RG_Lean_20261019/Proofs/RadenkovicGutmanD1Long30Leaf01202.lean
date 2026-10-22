/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01202 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack true 1167627735082937610410131456000000000000 1354614558053444933371075666410930700288 83597077192714129690568163328000000000000))
theorem leaf01202_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    true 1167627735082937610410131456000000000000 1354614558053444933371075666410930700288 83597077192714129690568163328000000000000 raw01202=true := by decide +kernel
#print axioms leaf01202_raw
theorem leaf01202_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01202=true := by decide +kernel
#print axioms leaf01202_rectangular
def affine01202 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01202 (IntegerComputedClassCell.leftNumerator ![(23/64),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(23/64),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.denominator ![(23/64),0,(3/4)] ![(1/64),1,(1/8)]))
theorem leaf01202_transform : affine01202=(NestedInteger.clearedAll 3 raw01202 (IntegerComputedClassCell.leftNumerator ![(23/64),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(23/64),0,(3/4)] ![(1/64),1,(1/8)]) (IntegerComputedClassCell.denominator ![(23/64),0,(3/4)] ![(1/64),1,(1/8)])) := by decide +kernel
#print axioms leaf01202_transform
theorem leaf01202_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01202=true := by decide +kernel
#print axioms leaf01202_sign
theorem leaf01202_log : RationalLog.accepts (612915031/536870912) (142237115/2147483648) 0 8=true := by decide +kernel
#print axioms leaf01202_log
def leaf01202 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack true (8102044973/500000000000) (612915031/536870912) (142237115/2147483648) 0 8 ![60,0,4] ![(23/64),0,(3/4)] ![(1/64),1,(1/8)] affine01202
theorem leaf01202_checked : FastNestedCellData.accepts 1 2 4 leaf01202=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack true (8102044973/500000000000) (612915031/536870912) (142237115/2147483648) 0 8 ![60,0,4] ![(23/64),0,(3/4)] ![(1/64),1,(1/8)] 1167627735082937610410131456000000000000 1354614558053444933371075666410930700288 83597077192714129690568163328000000000000 raw01202 affine01202
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01202_raw leaf01202_rectangular
    leaf01202_transform leaf01202_sign leaf01202_log
#print axioms leaf01202_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
