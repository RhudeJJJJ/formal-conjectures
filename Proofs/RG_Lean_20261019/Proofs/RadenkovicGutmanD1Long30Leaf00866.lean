/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00866 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 209301307640143048059815723008000000000000 55290681252168310173184474373335476600832 76141205397516247856500965376000000000000))
theorem leaf00866_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 209301307640143048059815723008000000000000 55290681252168310173184474373335476600832 76141205397516247856500965376000000000000 raw00866=true := by decide +kernel
#print axioms leaf00866_raw
theorem leaf00866_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00866=true := by decide +kernel
#print axioms leaf00866_rectangular
def affine00866 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00866 (IntegerComputedClassCell.leftNumerator ![(37/640),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(37/640),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(37/640),0,(1/16)] ![(1/640),1,(1/16)]))
theorem leaf00866_transform : affine00866=(NestedInteger.clearedAll 3 raw00866 (IntegerComputedClassCell.leftNumerator ![(37/640),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(37/640),0,(1/16)] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(37/640),0,(1/16)] ![(1/640),1,(1/16)])) := by decide +kernel
#print axioms leaf00866_transform
theorem leaf00866_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00866=true := by decide +kernel
#print axioms leaf00866_sign
theorem leaf00866_log : RationalLog.accepts (657292787/4294967296) (-503872063/536870912) 3 8=true := by decide +kernel
#print axioms leaf00866_log
def leaf00866 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (90769972979/125000000000) (657292787/4294967296) (-503872063/536870912) 3 8 ![60,0,4] ![(37/640),0,(1/16)] ![(1/640),1,(1/16)] affine00866
theorem leaf00866_checked : FastNestedCellData.accepts 1 2 4 leaf00866=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (90769972979/125000000000) (657292787/4294967296) (-503872063/536870912) 3 8 ![60,0,4] ![(37/640),0,(1/16)] ![(1/640),1,(1/16)] 209301307640143048059815723008000000000000 55290681252168310173184474373335476600832 76141205397516247856500965376000000000000 raw00866 affine00866
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00866_raw leaf00866_rectangular
    leaf00866_transform leaf00866_sign leaf00866_log
#print axioms leaf00866_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
