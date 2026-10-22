/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00289 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 12251853618359722990368718848000000000000 11583677860464500390848728027027499646976 484464427407306498107320041472000000000000))
theorem leaf00289_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 12251853618359722990368718848000000000000 11583677860464500390848728027027499646976 484464427407306498107320041472000000000000 raw00289=true := by decide +kernel
#print axioms leaf00289_raw
theorem leaf00289_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00289=true := by decide +kernel
#print axioms leaf00289_rectangular
def affine00289 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00289 (IntegerComputedClassCell.leftNumerator ![(41/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(41/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(41/6400),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00289_transform : affine00289=(NestedInteger.clearedAll 3 raw00289 (IntegerComputedClassCell.leftNumerator ![(41/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(41/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(41/6400),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00289_transform
theorem leaf00289_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00289=true := by decide +kernel
#print axioms leaf00289_sign
theorem leaf00289_log : RationalLog.accepts (3965907969/4294967296) (-42793515/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00289_log
def leaf00289 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (11955137679/500000000000) (3965907969/4294967296) (-42793515/1073741824) 1 8 ![60,0,4] ![(41/6400),0,(1/2)] ![(1/6400),1,(1/2)] affine00289
theorem leaf00289_checked : FastNestedCellData.accepts 1 2 4 leaf00289=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (11955137679/500000000000) (3965907969/4294967296) (-42793515/1073741824) 1 8 ![60,0,4] ![(41/6400),0,(1/2)] ![(1/6400),1,(1/2)] 12251853618359722990368718848000000000000 11583677860464500390848728027027499646976 484464427407306498107320041472000000000000 raw00289 affine00289
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00289_raw leaf00289_rectangular
    leaf00289_transform leaf00289_sign leaf00289_log
#print axioms leaf00289_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
