/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00274 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 102314668251121871853323288576000000000000 97109514804220309033401917783568090660864 4377071238502302679646764793856000000000000))
theorem leaf00274_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 102314668251121871853323288576000000000000 97109514804220309033401917783568090660864 4377071238502302679646764793856000000000000 raw00274=true := by decide +kernel
#print axioms leaf00274_raw
theorem leaf00274_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00274=true := by decide +kernel
#print axioms leaf00274_rectangular
def affine00274 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00274 (IntegerComputedClassCell.leftNumerator ![(19/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/3200),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00274_transform : affine00274=(NestedInteger.clearedAll 3 raw00274 (IntegerComputedClassCell.leftNumerator ![(19/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(19/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(19/3200),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00274_transform
theorem leaf00274_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00274=true := by decide +kernel
#print axioms leaf00274_sign
theorem leaf00274_log : RationalLog.accepts (1993993963/2147483648) (-159251231/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00274_log
def leaf00274 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (22185957119/1000000000000) (1993993963/2147483648) (-159251231/4294967296) 1 8 ![60,0,4] ![(19/3200),0,(1/2)] ![(1/6400),1,(1/2)] affine00274
theorem leaf00274_checked : FastNestedCellData.accepts 1 2 4 leaf00274=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (22185957119/1000000000000) (1993993963/2147483648) (-159251231/4294967296) 1 8 ![60,0,4] ![(19/3200),0,(1/2)] ![(1/6400),1,(1/2)] 102314668251121871853323288576000000000000 97109514804220309033401917783568090660864 4377071238502302679646764793856000000000000 raw00274 affine00274
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00274_raw leaf00274_rectangular
    leaf00274_transform leaf00274_sign leaf00274_log
#print axioms leaf00274_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
