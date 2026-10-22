/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw01015 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 11137128456087316114008883331072000000000000 6848244658183259142078055888708054856761344 11342943296537721811193227640832000000000000))
theorem leaf01015_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 11137128456087316114008883331072000000000000 6848244658183259142078055888708054856761344 11342943296537721811193227640832000000000000 raw01015=true := by decide +kernel
#print axioms leaf01015_raw
theorem leaf01015_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw01015=true := by decide +kernel
#print axioms leaf01015_rectangular
def affine01015 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw01015 (IntegerComputedClassCell.leftNumerator ![(7/40),0,0] ![(1/80),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/40),0,0] ![(1/80),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/40),0,0] ![(1/80),1,(1/16)]))
theorem leaf01015_transform : affine01015=(NestedInteger.clearedAll 3 raw01015 (IntegerComputedClassCell.leftNumerator ![(7/40),0,0] ![(1/80),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/40),0,0] ![(1/80),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/40),0,0] ![(1/80),1,(1/16)])) := by decide +kernel
#print axioms leaf01015_transform
theorem leaf01015_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine01015=true := by decide +kernel
#print axioms leaf01015_sign
theorem leaf01015_log : RationalLog.accepts (1646761101/4294967296) (-2058649947/4294967296) 2 8=true := by decide +kernel
#print axioms leaf01015_log
def leaf01015 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (603744943367/1000000000000) (1646761101/4294967296) (-2058649947/4294967296) 2 8 ![60,0,4] ![(7/40),0,0] ![(1/80),1,(1/16)] affine01015
theorem leaf01015_checked : FastNestedCellData.accepts 1 2 4 leaf01015=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (603744943367/1000000000000) (1646761101/4294967296) (-2058649947/4294967296) 2 8 ![60,0,4] ![(7/40),0,0] ![(1/80),1,(1/16)] 11137128456087316114008883331072000000000000 6848244658183259142078055888708054856761344 11342943296537721811193227640832000000000000 raw01015 affine01015
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf01015_raw leaf01015_rectangular
    leaf01015_transform leaf01015_sign leaf01015_log
#print axioms leaf01015_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
