/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00749 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 548705540195690575752266252288000000000000 428065040681764212691663309762662619938816 3597743085272291240197622857728000000000000))
theorem leaf00749_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 548705540195690575752266252288000000000000 428065040681764212691663309762662619938816 3597743085272291240197622857728000000000000 raw00749=true := by decide +kernel
#print axioms leaf00749_raw
theorem leaf00749_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00749=true := by decide +kernel
#print axioms leaf00749_rectangular
def affine00749 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00749 (IntegerComputedClassCell.leftNumerator ![(53/1600),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(53/1600),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(53/1600),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00749_transform : affine00749=(NestedInteger.clearedAll 3 raw00749 (IntegerComputedClassCell.leftNumerator ![(53/1600),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(53/1600),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(53/1600),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00749_transform
theorem leaf00749_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00749=true := by decide +kernel
#print axioms leaf00749_sign
theorem leaf00749_log : RationalLog.accepts (1497191513/2147483648) (-774609697/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00749_log
def leaf00749 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (118981547747/1000000000000) (1497191513/2147483648) (-774609697/4294967296) 1 8 ![60,0,4] ![(53/1600),0,(1/2)] ![(3/6400),1,(1/2)] affine00749
theorem leaf00749_checked : FastNestedCellData.accepts 1 2 4 leaf00749=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (118981547747/1000000000000) (1497191513/2147483648) (-774609697/4294967296) 1 8 ![60,0,4] ![(53/1600),0,(1/2)] ![(3/6400),1,(1/2)] 548705540195690575752266252288000000000000 428065040681764212691663309762662619938816 3597743085272291240197622857728000000000000 raw00749 affine00749
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00749_raw leaf00749_rectangular
    leaf00749_transform leaf00749_sign leaf00749_log
#print axioms leaf00749_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
