/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00656 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 10489841330595614709727025430528000000000000 3130953329214340626702128992852984801001472 5505888311417046060141991952384000000000000))
theorem leaf00656_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 10489841330595614709727025430528000000000000 3130953329214340626702128992852984801001472 5505888311417046060141991952384000000000000 raw00656=true := by decide +kernel
#print axioms leaf00656_raw
theorem leaf00656_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00656=true := by decide +kernel
#print axioms leaf00656_rectangular
def affine00656 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00656 (IntegerComputedClassCell.leftNumerator ![(79/3200),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(79/3200),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(79/3200),0,(1/16)] ![(3/6400),1,(1/16)]))
theorem leaf00656_transform : affine00656=(NestedInteger.clearedAll 3 raw00656 (IntegerComputedClassCell.leftNumerator ![(79/3200),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(79/3200),0,(1/16)] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(79/3200),0,(1/16)] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00656_transform
theorem leaf00656_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00656=true := by decide +kernel
#print axioms leaf00656_sign
theorem leaf00656_log : RationalLog.accepts (817221863/4294967296) (-1781647625/2147483648) 3 8=true := by decide +kernel
#print axioms leaf00656_log
def leaf00656 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (568655437983/1000000000000) (817221863/4294967296) (-1781647625/2147483648) 3 8 ![60,0,4] ![(79/3200),0,(1/16)] ![(3/6400),1,(1/16)] affine00656
theorem leaf00656_checked : FastNestedCellData.accepts 1 2 4 leaf00656=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (568655437983/1000000000000) (817221863/4294967296) (-1781647625/2147483648) 3 8 ![60,0,4] ![(79/3200),0,(1/16)] ![(3/6400),1,(1/16)] 10489841330595614709727025430528000000000000 3130953329214340626702128992852984801001472 5505888311417046060141991952384000000000000 raw00656 affine00656
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00656_raw leaf00656_rectangular
    leaf00656_transform leaf00656_sign leaf00656_log
#print axioms leaf00656_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
