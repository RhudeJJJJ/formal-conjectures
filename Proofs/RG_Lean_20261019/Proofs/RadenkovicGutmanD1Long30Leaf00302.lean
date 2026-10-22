/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00302 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 658277872090818108313951010816000000000000 517039326564244495934590157605098598957056 4829618077484611931871958269952000000000000))
theorem leaf00302_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 658277872090818108313951010816000000000000 517039326564244495934590157605098598957056 4829618077484611931871958269952000000000000 raw00302=true := by decide +kernel
#print axioms leaf00302_raw
theorem leaf00302_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00302=true := by decide +kernel
#print axioms leaf00302_rectangular
def affine00302 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00302 (IntegerComputedClassCell.leftNumerator ![(11/1600),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(11/1600),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(11/1600),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00302_transform : affine00302=(NestedInteger.clearedAll 3 raw00302 (IntegerComputedClassCell.leftNumerator ![(11/1600),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(11/1600),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(11/1600),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00302_transform
theorem leaf00302_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00302=true := by decide +kernel
#print axioms leaf00302_sign
theorem leaf00302_log : RationalLog.accepts (3047225637/4294967296) (-368521517/2147483648) 1 8=true := by decide +kernel
#print axioms leaf00302_log
def leaf00302 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (107055944853/1000000000000) (3047225637/4294967296) (-368521517/2147483648) 1 8 ![60,0,4] ![(11/1600),0,(1/8)] ![(1/6400),1,(1/8)] affine00302
theorem leaf00302_checked : FastNestedCellData.accepts 1 2 4 leaf00302=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (107055944853/1000000000000) (3047225637/4294967296) (-368521517/2147483648) 1 8 ![60,0,4] ![(11/1600),0,(1/8)] ![(1/6400),1,(1/8)] 658277872090818108313951010816000000000000 517039326564244495934590157605098598957056 4829618077484611931871958269952000000000000 raw00302 affine00302
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00302_raw leaf00302_rectangular
    leaf00302_transform leaf00302_sign leaf00302_log
#print axioms leaf00302_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
