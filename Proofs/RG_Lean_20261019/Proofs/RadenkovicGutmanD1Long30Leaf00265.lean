/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00265 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 110669572703567164356047772057600000000000 97119772602793954789046033227274256384 202352772529822758200147968000000000000))
theorem leaf00265_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 110669572703567164356047772057600000000000 97119772602793954789046033227274256384 202352772529822758200147968000000000000 raw00265=true := by decide +kernel
#print axioms leaf00265_raw
theorem leaf00265_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00265=true := by decide +kernel
#print axioms leaf00265_rectangular
def affine00265 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00265 (IntegerComputedClassCell.leftNumerator ![(37/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(37/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(37/6400),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00265_transform : affine00265=(NestedInteger.clearedAll 3 raw00265 (IntegerComputedClassCell.leftNumerator ![(37/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(37/6400),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(37/6400),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00265_transform
theorem leaf00265_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00265=true := by decide +kernel
#print axioms leaf00265_sign
theorem leaf00265_log : RationalLog.accepts (636695/1073741824) (-15956597181/4294967296) 11 8=true := by decide +kernel
#print axioms leaf00265_log
def leaf00265 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (479952764613/1000000000000) (636695/1073741824) (-15956597181/4294967296) 11 8 ![60,0,4] ![(37/6400),0,0] ![(1/6400),1,(1/16)] affine00265
theorem leaf00265_checked : FastNestedCellData.accepts 1 2 4 leaf00265=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (479952764613/1000000000000) (636695/1073741824) (-15956597181/4294967296) 11 8 ![60,0,4] ![(37/6400),0,0] ![(1/6400),1,(1/16)] 110669572703567164356047772057600000000000 97119772602793954789046033227274256384 202352772529822758200147968000000000000 raw00265 affine00265
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00265_raw leaf00265_rectangular
    leaf00265_transform leaf00265_sign leaf00265_log
#print axioms leaf00265_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
