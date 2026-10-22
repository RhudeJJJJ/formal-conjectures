/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00363 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1849905839588784519040204800000000000 1421052649965552076039295311181512704 2702777845456337461313536000000000000))
theorem leaf00363_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1849905839588784519040204800000000000 1421052649965552076039295311181512704 2702777845456337461313536000000000000 raw00363=true := by decide +kernel
#print axioms leaf00363_raw
theorem leaf00363_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00363=true := by decide +kernel
#print axioms leaf00363_rectangular
def affine00363 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00363 (IntegerComputedClassCell.leftNumerator ![(19/80),0,0] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/80),0,0] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/80),0,0] ![(3/160),1,(1/4)]))
theorem leaf00363_transform : affine00363=(NestedInteger.clearedAll 3 raw00363 (IntegerComputedClassCell.leftNumerator ![(19/80),0,0] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/80),0,0] ![(3/160),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/80),0,0] ![(3/160),1,(1/4)])) := by decide +kernel
#print axioms leaf00363_transform
theorem leaf00363_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00363=true := by decide +kernel
#print axioms leaf00363_sign
theorem leaf00363_log : RationalLog.accepts (270296215/536870912) (-1473687557/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00363_log
def leaf00363 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (4107616113/7812500000) (270296215/536870912) (-1473687557/4294967296) 1 8 ![52,0,4] ![(19/80),0,0] ![(3/160),1,(1/4)] affine00363
theorem leaf00363_checked : FastNestedCellData.accepts 1 0 4 leaf00363=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (4107616113/7812500000) (270296215/536870912) (-1473687557/4294967296) 1 8 ![52,0,4] ![(19/80),0,0] ![(3/160),1,(1/4)] 1849905839588784519040204800000000000 1421052649965552076039295311181512704 2702777845456337461313536000000000000 raw00363 affine00363
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00363_raw leaf00363_rectangular
    leaf00363_transform leaf00363_sign leaf00363_log
#print axioms leaf00363_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
