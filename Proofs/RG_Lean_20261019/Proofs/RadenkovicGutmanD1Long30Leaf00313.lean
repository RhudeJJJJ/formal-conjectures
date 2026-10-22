/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00313 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 794340286799360210697086566400000000000 700040520790105794035736005552275193856 12700661541527575793749721088000000000000))
theorem leaf00313_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 794340286799360210697086566400000000000 700040520790105794035736005552275193856 12700661541527575793749721088000000000000 raw00313=true := by decide +kernel
#print axioms leaf00313_raw
theorem leaf00313_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00313=true := by decide +kernel
#print axioms leaf00313_rectangular
def affine00313 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00313 (IntegerComputedClassCell.leftNumerator ![(23/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/3200),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00313_transform : affine00313=(NestedInteger.clearedAll 3 raw00313 (IntegerComputedClassCell.leftNumerator ![(23/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(23/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(23/3200),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00313_transform
theorem leaf00313_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00313=true := by decide +kernel
#print axioms leaf00313_sign
theorem leaf00313_log : RationalLog.accepts (224210145/268435456) (-386604513/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00313_log
def leaf00313 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (55118429737/1000000000000) (224210145/268435456) (-386604513/4294967296) 1 8 ![60,0,4] ![(23/3200),0,(1/4)] ![(1/6400),1,(1/4)] affine00313
theorem leaf00313_checked : FastNestedCellData.accepts 1 2 4 leaf00313=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (55118429737/1000000000000) (224210145/268435456) (-386604513/4294967296) 1 8 ![60,0,4] ![(23/3200),0,(1/4)] ![(1/6400),1,(1/4)] 794340286799360210697086566400000000000 700040520790105794035736005552275193856 12700661541527575793749721088000000000000 raw00313 affine00313
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00313_raw leaf00313_rectangular
    leaf00313_transform leaf00313_sign leaf00313_log
#print axioms leaf00313_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
