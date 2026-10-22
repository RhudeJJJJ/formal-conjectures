/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanPaidDegreeOneClass
import Proofs.RadenkovicGutmanD1Short13Cells00
import Proofs.RadenkovicGutmanD1Short13Cells01
import Proofs.RadenkovicGutmanD1Short13Cells02
import Proofs.RadenkovicGutmanD1Short13Cells03
import Proofs.RadenkovicGutmanD1Short13Cells04
import Proofs.RadenkovicGutmanD1Short13Cells05
import Proofs.RadenkovicGutmanD1Short13Cells06
import Proofs.RadenkovicGutmanD1Short13Cells07
import Proofs.RadenkovicGutmanD1Short13Cells08
import Proofs.RadenkovicGutmanD1Short13Cells09
import Proofs.RadenkovicGutmanD1Short13Cells10
import Proofs.RadenkovicGutmanD1Short13Cells11
import Proofs.RadenkovicGutmanD1Short13Cells12
import Proofs.RadenkovicGutmanD1Short13Cells13
import Proofs.RadenkovicGutmanD1Short13Cells14
import Proofs.RadenkovicGutmanD1Short13Cells15
namespace Gebendorfer.RadenkovicGutman.DegreeOneShortClass13
open CellPartition
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def slice000 : Slice := ⟨cell000,(1/1000),(1/500)⟩
theorem slice000_checked : CellPartition.accepts 1 0 2 slice000=true :=
  accepts_of_checks 1 0 2 slice000 cell000_checked (by decide +kernel)
def slice001 : Slice := ⟨cell001,(1/500),(7/2000)⟩
theorem slice001_checked : CellPartition.accepts 1 0 2 slice001=true :=
  accepts_of_checks 1 0 2 slice001 cell001_checked (by decide +kernel)
def slice002 : Slice := ⟨cell002,(7/2000),(1/200)⟩
theorem slice002_checked : CellPartition.accepts 1 0 2 slice002=true :=
  accepts_of_checks 1 0 2 slice002 cell002_checked (by decide +kernel)
def slice003 : Slice := ⟨cell003,(1/200),(3/400)⟩
theorem slice003_checked : CellPartition.accepts 1 0 2 slice003=true :=
  accepts_of_checks 1 0 2 slice003 cell003_checked (by decide +kernel)
def slice004 : Slice := ⟨cell004,(3/400),(1/100)⟩
theorem slice004_checked : CellPartition.accepts 1 0 2 slice004=true :=
  accepts_of_checks 1 0 2 slice004 cell004_checked (by decide +kernel)
def slice005 : Slice := ⟨cell005,(1/100),(1/80)⟩
theorem slice005_checked : CellPartition.accepts 1 0 2 slice005=true :=
  accepts_of_checks 1 0 2 slice005 cell005_checked (by decide +kernel)
def slice006 : Slice := ⟨cell006,(1/80),(3/200)⟩
theorem slice006_checked : CellPartition.accepts 1 0 2 slice006=true :=
  accepts_of_checks 1 0 2 slice006 cell006_checked (by decide +kernel)
def slice007 : Slice := ⟨cell007,(3/200),(7/400)⟩
theorem slice007_checked : CellPartition.accepts 1 0 2 slice007=true :=
  accepts_of_checks 1 0 2 slice007 cell007_checked (by decide +kernel)
def slice008 : Slice := ⟨cell008,(7/400),(1/50)⟩
theorem slice008_checked : CellPartition.accepts 1 0 2 slice008=true :=
  accepts_of_checks 1 0 2 slice008 cell008_checked (by decide +kernel)
def slice009 : Slice := ⟨cell009,(1/50),(19/800)⟩
theorem slice009_checked : CellPartition.accepts 1 0 2 slice009=true :=
  accepts_of_checks 1 0 2 slice009 cell009_checked (by decide +kernel)
def slice010 : Slice := ⟨cell010,(19/800),(11/400)⟩
theorem slice010_checked : CellPartition.accepts 1 0 2 slice010=true :=
  accepts_of_checks 1 0 2 slice010 cell010_checked (by decide +kernel)
def slice011 : Slice := ⟨cell011,(11/400),(1/32)⟩
theorem slice011_checked : CellPartition.accepts 1 0 2 slice011=true :=
  accepts_of_checks 1 0 2 slice011 cell011_checked (by decide +kernel)
def slice012 : Slice := ⟨cell012,(1/32),(7/200)⟩
theorem slice012_checked : CellPartition.accepts 1 0 2 slice012=true :=
  accepts_of_checks 1 0 2 slice012 cell012_checked (by decide +kernel)
def slice013 : Slice := ⟨cell013,(7/200),(31/800)⟩
theorem slice013_checked : CellPartition.accepts 1 0 2 slice013=true :=
  accepts_of_checks 1 0 2 slice013 cell013_checked (by decide +kernel)
def slice014 : Slice := ⟨cell014,(31/800),(17/400)⟩
theorem slice014_checked : CellPartition.accepts 1 0 2 slice014=true :=
  accepts_of_checks 1 0 2 slice014 cell014_checked (by decide +kernel)
def slice015 : Slice := ⟨cell015,(17/400),(1/20)⟩
theorem slice015_checked : CellPartition.accepts 1 0 2 slice015=true :=
  accepts_of_checks 1 0 2 slice015 cell015_checked (by decide +kernel)
def slice016 : Slice := ⟨cell016,(1/20),(9/160)⟩
theorem slice016_checked : CellPartition.accepts 1 0 2 slice016=true :=
  accepts_of_checks 1 0 2 slice016 cell016_checked (by decide +kernel)
def slice017 : Slice := ⟨cell017,(9/160),(1/16)⟩
theorem slice017_checked : CellPartition.accepts 1 0 2 slice017=true :=
  accepts_of_checks 1 0 2 slice017 cell017_checked (by decide +kernel)
def slice018 : Slice := ⟨cell018,(1/16),(11/160)⟩
theorem slice018_checked : CellPartition.accepts 1 0 2 slice018=true :=
  accepts_of_checks 1 0 2 slice018 cell018_checked (by decide +kernel)
def slice019 : Slice := ⟨cell019,(11/160),(3/40)⟩
theorem slice019_checked : CellPartition.accepts 1 0 2 slice019=true :=
  accepts_of_checks 1 0 2 slice019 cell019_checked (by decide +kernel)
def slice020 : Slice := ⟨cell020,(3/40),(13/160)⟩
theorem slice020_checked : CellPartition.accepts 1 0 2 slice020=true :=
  accepts_of_checks 1 0 2 slice020 cell020_checked (by decide +kernel)
def slice021 : Slice := ⟨cell021,(13/160),(7/80)⟩
theorem slice021_checked : CellPartition.accepts 1 0 2 slice021=true :=
  accepts_of_checks 1 0 2 slice021 cell021_checked (by decide +kernel)
def slice022 : Slice := ⟨cell022,(7/80),(3/32)⟩
theorem slice022_checked : CellPartition.accepts 1 0 2 slice022=true :=
  accepts_of_checks 1 0 2 slice022 cell022_checked (by decide +kernel)
def slice023 : Slice := ⟨cell023,(3/32),(1/10)⟩
theorem slice023_checked : CellPartition.accepts 1 0 2 slice023=true :=
  accepts_of_checks 1 0 2 slice023 cell023_checked (by decide +kernel)
def slice024 : Slice := ⟨cell024,(1/10),(17/160)⟩
theorem slice024_checked : CellPartition.accepts 1 0 2 slice024=true :=
  accepts_of_checks 1 0 2 slice024 cell024_checked (by decide +kernel)
def slice025 : Slice := ⟨cell025,(17/160),(9/80)⟩
theorem slice025_checked : CellPartition.accepts 1 0 2 slice025=true :=
  accepts_of_checks 1 0 2 slice025 cell025_checked (by decide +kernel)
def slice026 : Slice := ⟨cell026,(9/80),(1/8)⟩
theorem slice026_checked : CellPartition.accepts 1 0 2 slice026=true :=
  accepts_of_checks 1 0 2 slice026 cell026_checked (by decide +kernel)
def slice027 : Slice := ⟨cell027,(1/8),(11/80)⟩
theorem slice027_checked : CellPartition.accepts 1 0 2 slice027=true :=
  accepts_of_checks 1 0 2 slice027 cell027_checked (by decide +kernel)
def slice028 : Slice := ⟨cell028,(11/80),(3/20)⟩
theorem slice028_checked : CellPartition.accepts 1 0 2 slice028=true :=
  accepts_of_checks 1 0 2 slice028 cell028_checked (by decide +kernel)
def slice029 : Slice := ⟨cell029,(3/20),(13/80)⟩
theorem slice029_checked : CellPartition.accepts 1 0 2 slice029=true :=
  accepts_of_checks 1 0 2 slice029 cell029_checked (by decide +kernel)
def slice030 : Slice := ⟨cell030,(13/80),(7/40)⟩
theorem slice030_checked : CellPartition.accepts 1 0 2 slice030=true :=
  accepts_of_checks 1 0 2 slice030 cell030_checked (by decide +kernel)
def slice031 : Slice := ⟨cell031,(7/40),(3/16)⟩
theorem slice031_checked : CellPartition.accepts 1 0 2 slice031=true :=
  accepts_of_checks 1 0 2 slice031 cell031_checked (by decide +kernel)
def slice032 : Slice := ⟨cell032,(3/16),(1/5)⟩
theorem slice032_checked : CellPartition.accepts 1 0 2 slice032=true :=
  accepts_of_checks 1 0 2 slice032 cell032_checked (by decide +kernel)
def slice033 : Slice := ⟨cell033,(1/5),(7/32)⟩
theorem slice033_checked : CellPartition.accepts 1 0 2 slice033=true :=
  accepts_of_checks 1 0 2 slice033 cell033_checked (by decide +kernel)
def slice034 : Slice := ⟨cell034,(7/32),(19/80)⟩
theorem slice034_checked : CellPartition.accepts 1 0 2 slice034=true :=
  accepts_of_checks 1 0 2 slice034 cell034_checked (by decide +kernel)
def slice035 : Slice := ⟨cell035,(19/80),(41/160)⟩
theorem slice035_checked : CellPartition.accepts 1 0 2 slice035=true :=
  accepts_of_checks 1 0 2 slice035 cell035_checked (by decide +kernel)
def slice036 : Slice := ⟨cell036,(41/160),(11/40)⟩
theorem slice036_checked : CellPartition.accepts 1 0 2 slice036=true :=
  accepts_of_checks 1 0 2 slice036 cell036_checked (by decide +kernel)
def slice037 : Slice := ⟨cell037,(11/40),(47/160)⟩
theorem slice037_checked : CellPartition.accepts 1 0 2 slice037=true :=
  accepts_of_checks 1 0 2 slice037 cell037_checked (by decide +kernel)
def slice038 : Slice := ⟨cell038,(47/160),(5/16)⟩
theorem slice038_checked : CellPartition.accepts 1 0 2 slice038=true :=
  accepts_of_checks 1 0 2 slice038 cell038_checked (by decide +kernel)
def slice039 : Slice := ⟨cell039,(5/16),(53/160)⟩
theorem slice039_checked : CellPartition.accepts 1 0 2 slice039=true :=
  accepts_of_checks 1 0 2 slice039 cell039_checked (by decide +kernel)
def slice040 : Slice := ⟨cell040,(53/160),(7/20)⟩
theorem slice040_checked : CellPartition.accepts 1 0 2 slice040=true :=
  accepts_of_checks 1 0 2 slice040 cell040_checked (by decide +kernel)
def slice041 : Slice := ⟨cell041,(7/20),(59/160)⟩
theorem slice041_checked : CellPartition.accepts 1 0 2 slice041=true :=
  accepts_of_checks 1 0 2 slice041 cell041_checked (by decide +kernel)
def slice042 : Slice := ⟨cell042,(59/160),(31/80)⟩
theorem slice042_checked : CellPartition.accepts 1 0 2 slice042=true :=
  accepts_of_checks 1 0 2 slice042 cell042_checked (by decide +kernel)
def slice043 : Slice := ⟨cell043,(31/80),(13/32)⟩
theorem slice043_checked : CellPartition.accepts 1 0 2 slice043=true :=
  accepts_of_checks 1 0 2 slice043 cell043_checked (by decide +kernel)
def slice044 : Slice := ⟨cell044,(13/32),(17/40)⟩
theorem slice044_checked : CellPartition.accepts 1 0 2 slice044=true :=
  accepts_of_checks 1 0 2 slice044 cell044_checked (by decide +kernel)
def slice045 : Slice := ⟨cell045,(17/40),(37/80)⟩
theorem slice045_checked : CellPartition.accepts 1 0 2 slice045=true :=
  accepts_of_checks 1 0 2 slice045 cell045_checked (by decide +kernel)
def slice046 : Slice := ⟨cell046,(37/80),(1/2)⟩
theorem slice046_checked : CellPartition.accepts 1 0 2 slice046=true :=
  accepts_of_checks 1 0 2 slice046 cell046_checked (by decide +kernel)
def slice047 : Slice := ⟨cell047,(1/2),(17/32)⟩
theorem slice047_checked : CellPartition.accepts 1 0 2 slice047=true :=
  accepts_of_checks 1 0 2 slice047 cell047_checked (by decide +kernel)
def slice048 : Slice := ⟨cell048,(17/32),(9/16)⟩
theorem slice048_checked : CellPartition.accepts 1 0 2 slice048=true :=
  accepts_of_checks 1 0 2 slice048 cell048_checked (by decide +kernel)
def slice049 : Slice := ⟨cell049,(9/16),(19/32)⟩
theorem slice049_checked : CellPartition.accepts 1 0 2 slice049=true :=
  accepts_of_checks 1 0 2 slice049 cell049_checked (by decide +kernel)
def slice050 : Slice := ⟨cell050,(19/32),(5/8)⟩
theorem slice050_checked : CellPartition.accepts 1 0 2 slice050=true :=
  accepts_of_checks 1 0 2 slice050 cell050_checked (by decide +kernel)
def slice051 : Slice := ⟨cell051,(5/8),(21/32)⟩
theorem slice051_checked : CellPartition.accepts 1 0 2 slice051=true :=
  accepts_of_checks 1 0 2 slice051 cell051_checked (by decide +kernel)
def slice052 : Slice := ⟨cell052,(21/32),(11/16)⟩
theorem slice052_checked : CellPartition.accepts 1 0 2 slice052=true :=
  accepts_of_checks 1 0 2 slice052 cell052_checked (by decide +kernel)
def slice053 : Slice := ⟨cell053,(11/16),(3/4)⟩
theorem slice053_checked : CellPartition.accepts 1 0 2 slice053=true :=
  accepts_of_checks 1 0 2 slice053 cell053_checked (by decide +kernel)
def slice054 : Slice := ⟨cell054,(3/4),(13/16)⟩
theorem slice054_checked : CellPartition.accepts 1 0 2 slice054=true :=
  accepts_of_checks 1 0 2 slice054 cell054_checked (by decide +kernel)
def slice055 : Slice := ⟨cell055,(13/16),(7/8)⟩
theorem slice055_checked : CellPartition.accepts 1 0 2 slice055=true :=
  accepts_of_checks 1 0 2 slice055 cell055_checked (by decide +kernel)
def slice056 : Slice := ⟨cell056,(7/8),(15/16)⟩
theorem slice056_checked : CellPartition.accepts 1 0 2 slice056=true :=
  accepts_of_checks 1 0 2 slice056 cell056_checked (by decide +kernel)
def slice057 : Slice := ⟨cell057,(15/16),1⟩
theorem slice057_checked : CellPartition.accepts 1 0 2 slice057=true :=
  accepts_of_checks 1 0 2 slice057 cell057_checked (by decide +kernel)
def slice058 : Slice := ⟨cell058,1,(8/7)⟩
theorem slice058_checked : CellPartition.accepts 1 0 2 slice058=true :=
  accepts_of_checks 1 0 2 slice058 cell058_checked (by decide +kernel)
def slice059 : Slice := ⟨cell059,(8/7),(4/3)⟩
theorem slice059_checked : CellPartition.accepts 1 0 2 slice059=true :=
  accepts_of_checks 1 0 2 slice059 cell059_checked (by decide +kernel)
def slice060 : Slice := ⟨cell060,(4/3),(16/11)⟩
theorem slice060_checked : CellPartition.accepts 1 0 2 slice060=true :=
  accepts_of_checks 1 0 2 slice060 cell060_checked (by decide +kernel)
def slice061 : Slice := ⟨cell061,(16/11),(8/5)⟩
theorem slice061_checked : CellPartition.accepts 1 0 2 slice061=true :=
  accepts_of_checks 1 0 2 slice061 cell061_checked (by decide +kernel)
def slice062 : Slice := ⟨cell062,(8/5),(16/9)⟩
theorem slice062_checked : CellPartition.accepts 1 0 2 slice062=true :=
  accepts_of_checks 1 0 2 slice062 cell062_checked (by decide +kernel)
def slice063 : Slice := ⟨cell063,(16/9),(32/17)⟩
theorem slice063_checked : CellPartition.accepts 1 0 2 slice063=true :=
  accepts_of_checks 1 0 2 slice063 cell063_checked (by decide +kernel)
def slice064 : Slice := ⟨cell064,(32/17),2⟩
theorem slice064_checked : CellPartition.accepts 1 0 2 slice064=true :=
  accepts_of_checks 1 0 2 slice064 cell064_checked (by decide +kernel)
def slice065 : Slice := ⟨cell065,2,(32/15)⟩
theorem slice065_checked : CellPartition.accepts 1 0 2 slice065=true :=
  accepts_of_checks 1 0 2 slice065 cell065_checked (by decide +kernel)
def slice066 : Slice := ⟨cell066,(32/15),(16/7)⟩
theorem slice066_checked : CellPartition.accepts 1 0 2 slice066=true :=
  accepts_of_checks 1 0 2 slice066 cell066_checked (by decide +kernel)
def slice067 : Slice := ⟨cell067,(16/7),(32/13)⟩
theorem slice067_checked : CellPartition.accepts 1 0 2 slice067=true :=
  accepts_of_checks 1 0 2 slice067 cell067_checked (by decide +kernel)
def slice068 : Slice := ⟨cell068,(32/13),(64/25)⟩
theorem slice068_checked : CellPartition.accepts 1 0 2 slice068=true :=
  accepts_of_checks 1 0 2 slice068 cell068_checked (by decide +kernel)
def slice069 : Slice := ⟨cell069,(64/25),(8/3)⟩
theorem slice069_checked : CellPartition.accepts 1 0 2 slice069=true :=
  accepts_of_checks 1 0 2 slice069 cell069_checked (by decide +kernel)
def slice070 : Slice := ⟨cell070,(8/3),(64/23)⟩
theorem slice070_checked : CellPartition.accepts 1 0 2 slice070=true :=
  accepts_of_checks 1 0 2 slice070 cell070_checked (by decide +kernel)
def slice071 : Slice := ⟨cell071,(64/23),(32/11)⟩
theorem slice071_checked : CellPartition.accepts 1 0 2 slice071=true :=
  accepts_of_checks 1 0 2 slice071 cell071_checked (by decide +kernel)
def slice072 : Slice := ⟨cell072,(32/11),(64/21)⟩
theorem slice072_checked : CellPartition.accepts 1 0 2 slice072=true :=
  accepts_of_checks 1 0 2 slice072 cell072_checked (by decide +kernel)
def slice073 : Slice := ⟨cell073,(64/21),(16/5)⟩
theorem slice073_checked : CellPartition.accepts 1 0 2 slice073=true :=
  accepts_of_checks 1 0 2 slice073 cell073_checked (by decide +kernel)
def slice074 : Slice := ⟨cell074,(16/5),(64/19)⟩
theorem slice074_checked : CellPartition.accepts 1 0 2 slice074=true :=
  accepts_of_checks 1 0 2 slice074 cell074_checked (by decide +kernel)
def slice075 : Slice := ⟨cell075,(64/19),(32/9)⟩
theorem slice075_checked : CellPartition.accepts 1 0 2 slice075=true :=
  accepts_of_checks 1 0 2 slice075 cell075_checked (by decide +kernel)
def slice076 : Slice := ⟨cell076,(32/9),(64/17)⟩
theorem slice076_checked : CellPartition.accepts 1 0 2 slice076=true :=
  accepts_of_checks 1 0 2 slice076 cell076_checked (by decide +kernel)
def slice077 : Slice := ⟨cell077,(64/17),4⟩
theorem slice077_checked : CellPartition.accepts 1 0 2 slice077=true :=
  accepts_of_checks 1 0 2 slice077 cell077_checked (by decide +kernel)
def slice078 : Slice := ⟨cell078,4,(64/15)⟩
theorem slice078_checked : CellPartition.accepts 1 0 2 slice078=true :=
  accepts_of_checks 1 0 2 slice078 cell078_checked (by decide +kernel)
def slice079 : Slice := ⟨cell079,(64/15),(32/7)⟩
theorem slice079_checked : CellPartition.accepts 1 0 2 slice079=true :=
  accepts_of_checks 1 0 2 slice079 cell079_checked (by decide +kernel)
def slice080 : Slice := ⟨cell080,(32/7),(128/27)⟩
theorem slice080_checked : CellPartition.accepts 1 0 2 slice080=true :=
  accepts_of_checks 1 0 2 slice080 cell080_checked (by decide +kernel)
def slice081 : Slice := ⟨cell081,(128/27),(64/13)⟩
theorem slice081_checked : CellPartition.accepts 1 0 2 slice081=true :=
  accepts_of_checks 1 0 2 slice081 cell081_checked (by decide +kernel)
def slice082 : Slice := ⟨cell082,(64/13),(128/25)⟩
theorem slice082_checked : CellPartition.accepts 1 0 2 slice082=true :=
  accepts_of_checks 1 0 2 slice082 cell082_checked (by decide +kernel)
def slice083 : Slice := ⟨cell083,(128/25),(16/3)⟩
theorem slice083_checked : CellPartition.accepts 1 0 2 slice083=true :=
  accepts_of_checks 1 0 2 slice083 cell083_checked (by decide +kernel)
def slice084 : Slice := ⟨cell084,(16/3),(128/23)⟩
theorem slice084_checked : CellPartition.accepts 1 0 2 slice084=true :=
  accepts_of_checks 1 0 2 slice084 cell084_checked (by decide +kernel)
def slice085 : Slice := ⟨cell085,(128/23),(64/11)⟩
theorem slice085_checked : CellPartition.accepts 1 0 2 slice085=true :=
  accepts_of_checks 1 0 2 slice085 cell085_checked (by decide +kernel)
def slice086 : Slice := ⟨cell086,(64/11),(128/21)⟩
theorem slice086_checked : CellPartition.accepts 1 0 2 slice086=true :=
  accepts_of_checks 1 0 2 slice086 cell086_checked (by decide +kernel)
def slice087 : Slice := ⟨cell087,(128/21),(32/5)⟩
theorem slice087_checked : CellPartition.accepts 1 0 2 slice087=true :=
  accepts_of_checks 1 0 2 slice087 cell087_checked (by decide +kernel)
def slice088 : Slice := ⟨cell088,(32/5),(128/19)⟩
theorem slice088_checked : CellPartition.accepts 1 0 2 slice088=true :=
  accepts_of_checks 1 0 2 slice088 cell088_checked (by decide +kernel)
def slice089 : Slice := ⟨cell089,(128/19),(64/9)⟩
theorem slice089_checked : CellPartition.accepts 1 0 2 slice089=true :=
  accepts_of_checks 1 0 2 slice089 cell089_checked (by decide +kernel)
def slice090 : Slice := ⟨cell090,(64/9),(128/17)⟩
theorem slice090_checked : CellPartition.accepts 1 0 2 slice090=true :=
  accepts_of_checks 1 0 2 slice090 cell090_checked (by decide +kernel)
def slice091 : Slice := ⟨cell091,(128/17),8⟩
theorem slice091_checked : CellPartition.accepts 1 0 2 slice091=true :=
  accepts_of_checks 1 0 2 slice091 cell091_checked (by decide +kernel)
def slice092 : Slice := ⟨cell092,8,(128/15)⟩
theorem slice092_checked : CellPartition.accepts 1 0 2 slice092=true :=
  accepts_of_checks 1 0 2 slice092 cell092_checked (by decide +kernel)
def slice093 : Slice := ⟨cell093,(128/15),(64/7)⟩
theorem slice093_checked : CellPartition.accepts 1 0 2 slice093=true :=
  accepts_of_checks 1 0 2 slice093 cell093_checked (by decide +kernel)
def slice094 : Slice := ⟨cell094,(64/7),(128/13)⟩
theorem slice094_checked : CellPartition.accepts 1 0 2 slice094=true :=
  accepts_of_checks 1 0 2 slice094 cell094_checked (by decide +kernel)
def slice095 : Slice := ⟨cell095,(128/13),(32/3)⟩
theorem slice095_checked : CellPartition.accepts 1 0 2 slice095=true :=
  accepts_of_checks 1 0 2 slice095 cell095_checked (by decide +kernel)
def slice096 : Slice := ⟨cell096,(32/3),(128/11)⟩
theorem slice096_checked : CellPartition.accepts 1 0 2 slice096=true :=
  accepts_of_checks 1 0 2 slice096 cell096_checked (by decide +kernel)
def slice097 : Slice := ⟨cell097,(128/11),(256/21)⟩
theorem slice097_checked : CellPartition.accepts 1 0 2 slice097=true :=
  accepts_of_checks 1 0 2 slice097 cell097_checked (by decide +kernel)
def slice098 : Slice := ⟨cell098,(256/21),(64/5)⟩
theorem slice098_checked : CellPartition.accepts 1 0 2 slice098=true :=
  accepts_of_checks 1 0 2 slice098 cell098_checked (by decide +kernel)
def slice099 : Slice := ⟨cell099,(64/5),(256/19)⟩
theorem slice099_checked : CellPartition.accepts 1 0 2 slice099=true :=
  accepts_of_checks 1 0 2 slice099 cell099_checked (by decide +kernel)
def slice100 : Slice := ⟨cell100,(256/19),(128/9)⟩
theorem slice100_checked : CellPartition.accepts 1 0 2 slice100=true :=
  accepts_of_checks 1 0 2 slice100 cell100_checked (by decide +kernel)
def slice101 : Slice := ⟨cell101,(128/9),(256/17)⟩
theorem slice101_checked : CellPartition.accepts 1 0 2 slice101=true :=
  accepts_of_checks 1 0 2 slice101 cell101_checked (by decide +kernel)
def slice102 : Slice := ⟨cell102,(256/17),16⟩
theorem slice102_checked : CellPartition.accepts 1 0 2 slice102=true :=
  accepts_of_checks 1 0 2 slice102 cell102_checked (by decide +kernel)
def slice103 : Slice := ⟨cell103,16,(256/15)⟩
theorem slice103_checked : CellPartition.accepts 1 0 2 slice103=true :=
  accepts_of_checks 1 0 2 slice103 cell103_checked (by decide +kernel)
def slice104 : Slice := ⟨cell104,(256/15),(128/7)⟩
theorem slice104_checked : CellPartition.accepts 1 0 2 slice104=true :=
  accepts_of_checks 1 0 2 slice104 cell104_checked (by decide +kernel)
def slice105 : Slice := ⟨cell105,(128/7),(256/13)⟩
theorem slice105_checked : CellPartition.accepts 1 0 2 slice105=true :=
  accepts_of_checks 1 0 2 slice105 cell105_checked (by decide +kernel)
def slice106 : Slice := ⟨cell106,(256/13),(64/3)⟩
theorem slice106_checked : CellPartition.accepts 1 0 2 slice106=true :=
  accepts_of_checks 1 0 2 slice106 cell106_checked (by decide +kernel)
def slice107 : Slice := ⟨cell107,(64/3),(256/11)⟩
theorem slice107_checked : CellPartition.accepts 1 0 2 slice107=true :=
  accepts_of_checks 1 0 2 slice107 cell107_checked (by decide +kernel)
def slice108 : Slice := ⟨cell108,(256/11),(128/5)⟩
theorem slice108_checked : CellPartition.accepts 1 0 2 slice108=true :=
  accepts_of_checks 1 0 2 slice108 cell108_checked (by decide +kernel)
def slice109 : Slice := ⟨cell109,(128/5),(256/9)⟩
theorem slice109_checked : CellPartition.accepts 1 0 2 slice109=true :=
  accepts_of_checks 1 0 2 slice109 cell109_checked (by decide +kernel)
def slice110 : Slice := ⟨cell110,(256/9),32⟩
theorem slice110_checked : CellPartition.accepts 1 0 2 slice110=true :=
  accepts_of_checks 1 0 2 slice110 cell110_checked (by decide +kernel)
def slice111 : Slice := ⟨cell111,32,(256/7)⟩
theorem slice111_checked : CellPartition.accepts 1 0 2 slice111=true :=
  accepts_of_checks 1 0 2 slice111 cell111_checked (by decide +kernel)
def slice112 : Slice := ⟨cell112,(256/7),(128/3)⟩
theorem slice112_checked : CellPartition.accepts 1 0 2 slice112=true :=
  accepts_of_checks 1 0 2 slice112 cell112_checked (by decide +kernel)
def slice113 : Slice := ⟨cell113,(128/3),(512/11)⟩
theorem slice113_checked : CellPartition.accepts 1 0 2 slice113=true :=
  accepts_of_checks 1 0 2 slice113 cell113_checked (by decide +kernel)
def slice114 : Slice := ⟨cell114,(512/11),(256/5)⟩
theorem slice114_checked : CellPartition.accepts 1 0 2 slice114=true :=
  accepts_of_checks 1 0 2 slice114 cell114_checked (by decide +kernel)
def slice115 : Slice := ⟨cell115,(256/5),(512/9)⟩
theorem slice115_checked : CellPartition.accepts 1 0 2 slice115=true :=
  accepts_of_checks 1 0 2 slice115 cell115_checked (by decide +kernel)
def slice116 : Slice := ⟨cell116,(512/9),64⟩
theorem slice116_checked : CellPartition.accepts 1 0 2 slice116=true :=
  accepts_of_checks 1 0 2 slice116 cell116_checked (by decide +kernel)
def slice117 : Slice := ⟨cell117,64,(512/7)⟩
theorem slice117_checked : CellPartition.accepts 1 0 2 slice117=true :=
  accepts_of_checks 1 0 2 slice117 cell117_checked (by decide +kernel)
def slice118 : Slice := ⟨cell118,(512/7),(256/3)⟩
theorem slice118_checked : CellPartition.accepts 1 0 2 slice118=true :=
  accepts_of_checks 1 0 2 slice118 cell118_checked (by decide +kernel)
def slice119 : Slice := ⟨cell119,(256/3),(512/5)⟩
theorem slice119_checked : CellPartition.accepts 1 0 2 slice119=true :=
  accepts_of_checks 1 0 2 slice119 cell119_checked (by decide +kernel)
def slice120 : Slice := ⟨cell120,(512/5),128⟩
theorem slice120_checked : CellPartition.accepts 1 0 2 slice120=true :=
  accepts_of_checks 1 0 2 slice120 cell120_checked (by decide +kernel)
def slice121 : Slice := ⟨cell121,128,(512/3)⟩
theorem slice121_checked : CellPartition.accepts 1 0 2 slice121=true :=
  accepts_of_checks 1 0 2 slice121 cell121_checked (by decide +kernel)
def slice122 : Slice := ⟨cell122,(512/3),(1024/5)⟩
theorem slice122_checked : CellPartition.accepts 1 0 2 slice122=true :=
  accepts_of_checks 1 0 2 slice122 cell122_checked (by decide +kernel)
def slice123 : Slice := ⟨cell123,(1024/5),256⟩
theorem slice123_checked : CellPartition.accepts 1 0 2 slice123=true :=
  accepts_of_checks 1 0 2 slice123 cell123_checked (by decide +kernel)
def slice124 : Slice := ⟨cell124,256,(1024/3)⟩
theorem slice124_checked : CellPartition.accepts 1 0 2 slice124=true :=
  accepts_of_checks 1 0 2 slice124 cell124_checked (by decide +kernel)
def slice125 : Slice := ⟨cell125,(1024/3),512⟩
theorem slice125_checked : CellPartition.accepts 1 0 2 slice125=true :=
  accepts_of_checks 1 0 2 slice125 cell125_checked (by decide +kernel)
def slice126 : Slice := ⟨cell126,512,1024⟩
theorem slice126_checked : CellPartition.accepts 1 0 2 slice126=true :=
  accepts_of_checks 1 0 2 slice126 cell126_checked (by decide +kernel)
def partition : List Slice := [slice000,slice001,slice002,slice003,slice004,slice005,slice006,slice007,slice008,slice009,slice010,slice011,slice012,slice013,slice014,slice015,slice016,slice017,slice018,slice019,slice020,slice021,slice022,slice023,slice024,slice025,slice026,slice027,slice028,slice029,slice030,slice031,slice032,slice033,slice034,slice035,slice036,slice037,slice038,slice039,slice040,slice041,slice042,slice043,slice044,slice045,slice046,slice047,slice048,slice049,slice050,slice051,slice052,slice053,slice054,slice055,slice056,slice057,slice058,slice059,slice060,slice061,slice062,slice063,slice064,slice065,slice066,slice067,slice068,slice069,slice070,slice071,slice072,slice073,slice074,slice075,slice076,slice077,slice078,slice079,slice080,slice081,slice082,slice083,slice084,slice085,slice086,slice087,slice088,slice089,slice090,slice091,slice092,slice093,slice094,slice095,slice096,slice097,slice098,slice099,slice100,slice101,slice102,slice103,slice104,slice105,slice106,slice107,slice108,slice109,slice110,slice111,slice112,slice113,slice114,slice115,slice116,slice117,slice118,slice119,slice120,slice121,slice122,slice123,slice124,slice125,slice126]
theorem partition_checked : checkAt 1 0 2 (1/1000) 1024 partition=true := by
  unfold partition
  apply checked_cons _ _ _ _ _ _ _ rfl slice000_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice001_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice002_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice003_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice004_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice005_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice006_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice007_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice008_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice009_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice010_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice011_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice012_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice013_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice014_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice015_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice016_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice017_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice018_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice019_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice020_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice021_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice022_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice023_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice024_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice025_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice026_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice027_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice028_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice029_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice030_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice031_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice032_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice033_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice034_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice035_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice036_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice037_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice038_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice039_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice040_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice041_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice042_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice043_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice044_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice045_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice046_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice047_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice048_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice049_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice050_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice051_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice052_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice053_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice054_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice055_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice056_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice057_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice058_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice059_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice060_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice061_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice062_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice063_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice064_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice065_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice066_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice067_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice068_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice069_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice070_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice071_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice072_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice073_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice074_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice075_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice076_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice077_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice078_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice079_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice080_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice081_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice082_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice083_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice084_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice085_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice086_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice087_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice088_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice089_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice090_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice091_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice092_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice093_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice094_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice095_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice096_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice097_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice098_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice099_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice100_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice101_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice102_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice103_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice104_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice105_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice106_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice107_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice108_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice109_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice110_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice111_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice112_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice113_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice114_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice115_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice116_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice117_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice118_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice119_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice120_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice121_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice122_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice123_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice124_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice125_checked
  apply checked_cons _ _ _ _ _ _ _ rfl slice126_checked
  decide +kernel
theorem budget_checked : PaidDegreeOneClass.accepts (payment partition)=true := by decide +kernel
noncomputable section
open scoped Classical
theorem normalized_target {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (u : V) (p q : ℕ) (hd : C.degree u=1)
    (hp : ArmClasses.classify p=0) (hq : ArmClasses.classify q=2) :
    (189/5000 : ℝ) < ActualFusionIntegral.normalizedIntegral C u p q 2 :=
  PaidDegreeOneClass.normalized_target C u p q hd 0 2 hp hq
    partition partition_checked budget_checked
#print axioms partition_checked
#print axioms budget_checked
#print axioms normalized_target
end
end Gebendorfer.RadenkovicGutman.DegreeOneShortClass13
