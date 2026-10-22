/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00268 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 128312696912493933566414028800000000000 115733041767104613552513116131779674112 2599725433599412492331227545600000000000))
theorem leaf00268_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 128312696912493933566414028800000000000 115733041767104613552513116131779674112 2599725433599412492331227545600000000000 raw00268=true := by decide +kernel
#print axioms leaf00268_raw
theorem leaf00268_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00268=true := by decide +kernel
#print axioms leaf00268_rectangular
def affine00268 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00268 (IntegerComputedClassCell.leftNumerator ![(37/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/6400),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00268_transform : affine00268=(NestedInteger.clearedAll 3 raw00268 (IntegerComputedClassCell.leftNumerator ![(37/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(37/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(37/6400),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00268_transform
theorem leaf00268_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00268=true := by decide +kernel
#print axioms leaf00268_sign
theorem leaf00268_log : RationalLog.accepts (3708787177/4294967296) (-315119691/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00268_log
def leaf00268 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (556467619/12500000000) (3708787177/4294967296) (-315119691/4294967296) 1 8 ![60,0,4] ![(37/6400),0,(1/4)] ![(1/6400),1,(1/4)] affine00268
theorem leaf00268_checked : FastNestedCellData.accepts 1 2 4 leaf00268=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (556467619/12500000000) (3708787177/4294967296) (-315119691/4294967296) 1 8 ![60,0,4] ![(37/6400),0,(1/4)] ![(1/6400),1,(1/4)] 128312696912493933566414028800000000000 115733041767104613552513116131779674112 2599725433599412492331227545600000000000 raw00268 affine00268
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00268_raw leaf00268_rectangular
    leaf00268_transform leaf00268_sign leaf00268_log
#print axioms leaf00268_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
