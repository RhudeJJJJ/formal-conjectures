/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00487 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3527035738190357093479270580224000000000000 2327727547325193090928024788459502807547904 12174244188651887642826806132736000000000000))
theorem leaf00487_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3527035738190357093479270580224000000000000 2327727547325193090928024788459502807547904 12174244188651887642826806132736000000000000 raw00487=true := by decide +kernel
#print axioms leaf00487_raw
theorem leaf00487_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00487=true := by decide +kernel
#print axioms leaf00487_rectangular
def affine00487 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00487 (IntegerComputedClassCell.leftNumerator ![(81/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(81/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(81/6400),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00487_transform : affine00487=(NestedInteger.clearedAll 3 raw00487 (IntegerComputedClassCell.leftNumerator ![(81/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(81/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(81/6400),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00487_transform
theorem leaf00487_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00487=true := by decide +kernel
#print axioms leaf00487_sign
theorem leaf00487_log : RationalLog.accepts (2379562419/4294967296) (-158518477/536870912) 1 8=true := by decide +kernel
#print axioms leaf00487_log
def leaf00487 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (191200990489/1000000000000) (2379562419/4294967296) (-158518477/536870912) 1 8 ![60,0,4] ![(81/6400),0,(1/8)] ![(1/6400),1,(1/8)] affine00487
theorem leaf00487_checked : FastNestedCellData.accepts 1 2 4 leaf00487=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (191200990489/1000000000000) (2379562419/4294967296) (-158518477/536870912) 1 8 ![60,0,4] ![(81/6400),0,(1/8)] ![(1/6400),1,(1/8)] 3527035738190357093479270580224000000000000 2327727547325193090928024788459502807547904 12174244188651887642826806132736000000000000 raw00487 affine00487
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00487_raw leaf00487_rectangular
    leaf00487_transform leaf00487_sign leaf00487_log
#print axioms leaf00487_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
