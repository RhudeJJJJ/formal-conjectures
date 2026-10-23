/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanMean16FastBatch000
import Proofs.RadenkovicGutmanMean16FastBatch001
import Proofs.RadenkovicGutmanMean16FastBatch002
import Proofs.RadenkovicGutmanMean16FastBatch003
import Proofs.RadenkovicGutmanMean16FastBatch004
import Proofs.RadenkovicGutmanMean16FastBatch005
import Proofs.RadenkovicGutmanMean16FastBatch006
import Proofs.RadenkovicGutmanMean16FastBatch007
import Proofs.RadenkovicGutmanMean16FastBatch008
import Proofs.RadenkovicGutmanMean16FastBatch009
import Proofs.RadenkovicGutmanMean16FastBatch010
import Proofs.RadenkovicGutmanMean16FastBatch011
import Proofs.RadenkovicGutmanMean16FastBatch012
import Proofs.RadenkovicGutmanMean16FastBatch013
import Proofs.RadenkovicGutmanMean16FastBatch014
import Proofs.RadenkovicGutmanMean16FastBatch015
import Proofs.RadenkovicGutmanMean16FastBatch016
import Proofs.RadenkovicGutmanMean16FastBatch017
import Proofs.RadenkovicGutmanMean16FastBatch018
import Proofs.RadenkovicGutmanMean16FastBatch019
import Proofs.RadenkovicGutmanMean16FastBatch020
import Proofs.RadenkovicGutmanMean16FastBatch021
import Proofs.RadenkovicGutmanMean16FastBatch022
import Proofs.RadenkovicGutmanRationalIntegralPartition

namespace Gebendorfer.RadenkovicGutman.Mean16FinitePayment
open Set MeasureTheory RationalIntegralPartition
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def slices : List Slice := [
  ⟨Mean16FastPolynomialCell000.cell.a,Mean16FastPolynomialCell000.cell.b,Mean16FastPolynomialCell000.cell.total⟩,
  ⟨Mean16FastPolynomialCell001.cell.a,Mean16FastPolynomialCell001.cell.b,Mean16FastPolynomialCell001.cell.total⟩,
  ⟨Mean16FastPolynomialCell002.cell.a,Mean16FastPolynomialCell002.cell.b,Mean16FastPolynomialCell002.cell.total⟩,
  ⟨Mean16FastPolynomialCell003.cell.a,Mean16FastPolynomialCell003.cell.b,Mean16FastPolynomialCell003.cell.total⟩,
  ⟨Mean16FastPolynomialCell004.cell.a,Mean16FastPolynomialCell004.cell.b,Mean16FastPolynomialCell004.cell.total⟩,
  ⟨Mean16FastPolynomialCell005.cell.a,Mean16FastPolynomialCell005.cell.b,Mean16FastPolynomialCell005.cell.total⟩,
  ⟨Mean16FastPolynomialCell006.cell.a,Mean16FastPolynomialCell006.cell.b,Mean16FastPolynomialCell006.cell.total⟩,
  ⟨Mean16FastPolynomialCell007.cell.a,Mean16FastPolynomialCell007.cell.b,Mean16FastPolynomialCell007.cell.total⟩,
  ⟨Mean16FastPolynomialCell008.cell.a,Mean16FastPolynomialCell008.cell.b,Mean16FastPolynomialCell008.cell.total⟩,
  ⟨Mean16FastPolynomialCell009.cell.a,Mean16FastPolynomialCell009.cell.b,Mean16FastPolynomialCell009.cell.total⟩,
  ⟨Mean16FastPolynomialCell010.cell.a,Mean16FastPolynomialCell010.cell.b,Mean16FastPolynomialCell010.cell.total⟩,
  ⟨Mean16FastPolynomialCell011.cell.a,Mean16FastPolynomialCell011.cell.b,Mean16FastPolynomialCell011.cell.total⟩,
  ⟨Mean16FastPolynomialCell012.cell.a,Mean16FastPolynomialCell012.cell.b,Mean16FastPolynomialCell012.cell.total⟩,
  ⟨Mean16FastPolynomialCell013.cell.a,Mean16FastPolynomialCell013.cell.b,Mean16FastPolynomialCell013.cell.total⟩,
  ⟨Mean16FastPolynomialCell014.cell.a,Mean16FastPolynomialCell014.cell.b,Mean16FastPolynomialCell014.cell.total⟩,
  ⟨Mean16FastPolynomialCell015.cell.a,Mean16FastPolynomialCell015.cell.b,Mean16FastPolynomialCell015.cell.total⟩,
  ⟨Mean16FastPolynomialCell016.cell.a,Mean16FastPolynomialCell016.cell.b,Mean16FastPolynomialCell016.cell.total⟩,
  ⟨Mean16FastPolynomialCell017.cell.a,Mean16FastPolynomialCell017.cell.b,Mean16FastPolynomialCell017.cell.total⟩,
  ⟨Mean16FastPolynomialCell018.cell.a,Mean16FastPolynomialCell018.cell.b,Mean16FastPolynomialCell018.cell.total⟩,
  ⟨Mean16FastPolynomialCell019.cell.a,Mean16FastPolynomialCell019.cell.b,Mean16FastPolynomialCell019.cell.total⟩,
  ⟨Mean16FastPolynomialCell020.cell.a,Mean16FastPolynomialCell020.cell.b,Mean16FastPolynomialCell020.cell.total⟩,
  ⟨Mean16FastPolynomialCell021.cell.a,Mean16FastPolynomialCell021.cell.b,Mean16FastPolynomialCell021.cell.total⟩,
  ⟨Mean16FastPolynomialCell022.cell.a,Mean16FastPolynomialCell022.cell.b,Mean16FastPolynomialCell022.cell.total⟩,
  ⟨Mean16FastPolynomialCell023.cell.a,Mean16FastPolynomialCell023.cell.b,Mean16FastPolynomialCell023.cell.total⟩,
  ⟨Mean16FastPolynomialCell024.cell.a,Mean16FastPolynomialCell024.cell.b,Mean16FastPolynomialCell024.cell.total⟩,
  ⟨Mean16FastPolynomialCell025.cell.a,Mean16FastPolynomialCell025.cell.b,Mean16FastPolynomialCell025.cell.total⟩,
  ⟨Mean16FastPolynomialCell026.cell.a,Mean16FastPolynomialCell026.cell.b,Mean16FastPolynomialCell026.cell.total⟩,
  ⟨Mean16FastPolynomialCell027.cell.a,Mean16FastPolynomialCell027.cell.b,Mean16FastPolynomialCell027.cell.total⟩,
  ⟨Mean16FastPolynomialCell028.cell.a,Mean16FastPolynomialCell028.cell.b,Mean16FastPolynomialCell028.cell.total⟩,
  ⟨Mean16FastPolynomialCell029.cell.a,Mean16FastPolynomialCell029.cell.b,Mean16FastPolynomialCell029.cell.total⟩,
  ⟨Mean16FastPolynomialCell030.cell.a,Mean16FastPolynomialCell030.cell.b,Mean16FastPolynomialCell030.cell.total⟩,
  ⟨Mean16FastPolynomialCell031.cell.a,Mean16FastPolynomialCell031.cell.b,Mean16FastPolynomialCell031.cell.total⟩,
  ⟨Mean16FastPolynomialCell032.cell.a,Mean16FastPolynomialCell032.cell.b,Mean16FastPolynomialCell032.cell.total⟩,
  ⟨Mean16FastPolynomialCell033.cell.a,Mean16FastPolynomialCell033.cell.b,Mean16FastPolynomialCell033.cell.total⟩,
  ⟨Mean16FastPolynomialCell034.cell.a,Mean16FastPolynomialCell034.cell.b,Mean16FastPolynomialCell034.cell.total⟩,
  ⟨Mean16FastPolynomialCell035.cell.a,Mean16FastPolynomialCell035.cell.b,Mean16FastPolynomialCell035.cell.total⟩,
  ⟨Mean16FastPolynomialCell036.cell.a,Mean16FastPolynomialCell036.cell.b,Mean16FastPolynomialCell036.cell.total⟩,
  ⟨Mean16FastPolynomialCell037.cell.a,Mean16FastPolynomialCell037.cell.b,Mean16FastPolynomialCell037.cell.total⟩,
  ⟨Mean16FastPolynomialCell038.cell.a,Mean16FastPolynomialCell038.cell.b,Mean16FastPolynomialCell038.cell.total⟩,
  ⟨Mean16FastPolynomialCell039.cell.a,Mean16FastPolynomialCell039.cell.b,Mean16FastPolynomialCell039.cell.total⟩,
  ⟨Mean16FastPolynomialCell040.cell.a,Mean16FastPolynomialCell040.cell.b,Mean16FastPolynomialCell040.cell.total⟩,
  ⟨Mean16FastPolynomialCell041.cell.a,Mean16FastPolynomialCell041.cell.b,Mean16FastPolynomialCell041.cell.total⟩,
  ⟨Mean16FastPolynomialCell042.cell.a,Mean16FastPolynomialCell042.cell.b,Mean16FastPolynomialCell042.cell.total⟩,
  ⟨Mean16FastPolynomialCell043.cell.a,Mean16FastPolynomialCell043.cell.b,Mean16FastPolynomialCell043.cell.total⟩,
  ⟨Mean16FastPolynomialCell044.cell.a,Mean16FastPolynomialCell044.cell.b,Mean16FastPolynomialCell044.cell.total⟩,
  ⟨Mean16FastPolynomialCell045.cell.a,Mean16FastPolynomialCell045.cell.b,Mean16FastPolynomialCell045.cell.total⟩,
  ⟨Mean16FastPolynomialCell046.cell.a,Mean16FastPolynomialCell046.cell.b,Mean16FastPolynomialCell046.cell.total⟩,
  ⟨Mean16FastPolynomialCell047.cell.a,Mean16FastPolynomialCell047.cell.b,Mean16FastPolynomialCell047.cell.total⟩,
  ⟨Mean16FastPolynomialCell048.cell.a,Mean16FastPolynomialCell048.cell.b,Mean16FastPolynomialCell048.cell.total⟩,
  ⟨Mean16FastPolynomialCell049.cell.a,Mean16FastPolynomialCell049.cell.b,Mean16FastPolynomialCell049.cell.total⟩,
  ⟨Mean16FastPolynomialCell050.cell.a,Mean16FastPolynomialCell050.cell.b,Mean16FastPolynomialCell050.cell.total⟩,
  ⟨Mean16FastPolynomialCell051.cell.a,Mean16FastPolynomialCell051.cell.b,Mean16FastPolynomialCell051.cell.total⟩,
  ⟨Mean16FastPolynomialCell052.cell.a,Mean16FastPolynomialCell052.cell.b,Mean16FastPolynomialCell052.cell.total⟩,
  ⟨Mean16FastPolynomialCell053.cell.a,Mean16FastPolynomialCell053.cell.b,Mean16FastPolynomialCell053.cell.total⟩,
  ⟨Mean16FastPolynomialCell054.cell.a,Mean16FastPolynomialCell054.cell.b,Mean16FastPolynomialCell054.cell.total⟩,
  ⟨Mean16FastPolynomialCell055.cell.a,Mean16FastPolynomialCell055.cell.b,Mean16FastPolynomialCell055.cell.total⟩,
  ⟨Mean16FastPolynomialCell056.cell.a,Mean16FastPolynomialCell056.cell.b,Mean16FastPolynomialCell056.cell.total⟩,
  ⟨Mean16FastPolynomialCell057.cell.a,Mean16FastPolynomialCell057.cell.b,Mean16FastPolynomialCell057.cell.total⟩,
  ⟨Mean16FastPolynomialCell058.cell.a,Mean16FastPolynomialCell058.cell.b,Mean16FastPolynomialCell058.cell.total⟩,
  ⟨Mean16FastPolynomialCell059.cell.a,Mean16FastPolynomialCell059.cell.b,Mean16FastPolynomialCell059.cell.total⟩,
  ⟨Mean16FastPolynomialCell060.cell.a,Mean16FastPolynomialCell060.cell.b,Mean16FastPolynomialCell060.cell.total⟩,
  ⟨Mean16FastPolynomialCell061.cell.a,Mean16FastPolynomialCell061.cell.b,Mean16FastPolynomialCell061.cell.total⟩,
  ⟨Mean16FastPolynomialCell062.cell.a,Mean16FastPolynomialCell062.cell.b,Mean16FastPolynomialCell062.cell.total⟩,
  ⟨Mean16FastPolynomialCell063.cell.a,Mean16FastPolynomialCell063.cell.b,Mean16FastPolynomialCell063.cell.total⟩,
  ⟨Mean16FastPolynomialCell064.cell.a,Mean16FastPolynomialCell064.cell.b,Mean16FastPolynomialCell064.cell.total⟩,
  ⟨Mean16FastPolynomialCell065.cell.a,Mean16FastPolynomialCell065.cell.b,Mean16FastPolynomialCell065.cell.total⟩,
  ⟨Mean16FastPolynomialCell066.cell.a,Mean16FastPolynomialCell066.cell.b,Mean16FastPolynomialCell066.cell.total⟩,
  ⟨Mean16FastPolynomialCell067.cell.a,Mean16FastPolynomialCell067.cell.b,Mean16FastPolynomialCell067.cell.total⟩,
  ⟨Mean16FastPolynomialCell068.cell.a,Mean16FastPolynomialCell068.cell.b,Mean16FastPolynomialCell068.cell.total⟩,
  ⟨Mean16FastPolynomialCell069.cell.a,Mean16FastPolynomialCell069.cell.b,Mean16FastPolynomialCell069.cell.total⟩,
  ⟨Mean16FastPolynomialCell070.cell.a,Mean16FastPolynomialCell070.cell.b,Mean16FastPolynomialCell070.cell.total⟩,
  ⟨Mean16FastPolynomialCell071.cell.a,Mean16FastPolynomialCell071.cell.b,Mean16FastPolynomialCell071.cell.total⟩,
  ⟨Mean16FastPolynomialCell072.cell.a,Mean16FastPolynomialCell072.cell.b,Mean16FastPolynomialCell072.cell.total⟩,
  ⟨Mean16FastPolynomialCell073.cell.a,Mean16FastPolynomialCell073.cell.b,Mean16FastPolynomialCell073.cell.total⟩,
  ⟨Mean16FastPolynomialCell074.cell.a,Mean16FastPolynomialCell074.cell.b,Mean16FastPolynomialCell074.cell.total⟩,
  ⟨Mean16FastPolynomialCell075.cell.a,Mean16FastPolynomialCell075.cell.b,Mean16FastPolynomialCell075.cell.total⟩,
  ⟨Mean16FastPolynomialCell076.cell.a,Mean16FastPolynomialCell076.cell.b,Mean16FastPolynomialCell076.cell.total⟩,
  ⟨Mean16FastPolynomialCell077.cell.a,Mean16FastPolynomialCell077.cell.b,Mean16FastPolynomialCell077.cell.total⟩,
  ⟨Mean16FastPolynomialCell078.cell.a,Mean16FastPolynomialCell078.cell.b,Mean16FastPolynomialCell078.cell.total⟩,
  ⟨Mean16FastPolynomialCell079.cell.a,Mean16FastPolynomialCell079.cell.b,Mean16FastPolynomialCell079.cell.total⟩,
  ⟨Mean16FastPolynomialCell080.cell.a,Mean16FastPolynomialCell080.cell.b,Mean16FastPolynomialCell080.cell.total⟩,
  ⟨Mean16FastPolynomialCell081.cell.a,Mean16FastPolynomialCell081.cell.b,Mean16FastPolynomialCell081.cell.total⟩,
  ⟨Mean16FastPolynomialCell082.cell.a,Mean16FastPolynomialCell082.cell.b,Mean16FastPolynomialCell082.cell.total⟩,
  ⟨Mean16FastPolynomialCell083.cell.a,Mean16FastPolynomialCell083.cell.b,Mean16FastPolynomialCell083.cell.total⟩,
  ⟨Mean16FastPolynomialCell084.cell.a,Mean16FastPolynomialCell084.cell.b,Mean16FastPolynomialCell084.cell.total⟩,
  ⟨Mean16FastPolynomialCell085.cell.a,Mean16FastPolynomialCell085.cell.b,Mean16FastPolynomialCell085.cell.total⟩,
  ⟨Mean16FastPolynomialCell086.cell.a,Mean16FastPolynomialCell086.cell.b,Mean16FastPolynomialCell086.cell.total⟩,
  ⟨Mean16FastPolynomialCell087.cell.a,Mean16FastPolynomialCell087.cell.b,Mean16FastPolynomialCell087.cell.total⟩,
  ⟨Mean16FastPolynomialCell088.cell.a,Mean16FastPolynomialCell088.cell.b,Mean16FastPolynomialCell088.cell.total⟩,
  ⟨Mean16FastPolynomialCell089.cell.a,Mean16FastPolynomialCell089.cell.b,Mean16FastPolynomialCell089.cell.total⟩,
  ⟨Mean16FastPolynomialCell090.cell.a,Mean16FastPolynomialCell090.cell.b,Mean16FastPolynomialCell090.cell.total⟩,
  ⟨Mean16FastPolynomialCell091.cell.a,Mean16FastPolynomialCell091.cell.b,Mean16FastPolynomialCell091.cell.total⟩,
  ⟨Mean16FastPolynomialCell092.cell.a,Mean16FastPolynomialCell092.cell.b,Mean16FastPolynomialCell092.cell.total⟩,
  ⟨Mean16FastPolynomialCell093.cell.a,Mean16FastPolynomialCell093.cell.b,Mean16FastPolynomialCell093.cell.total⟩,
  ⟨Mean16FastPolynomialCell094.cell.a,Mean16FastPolynomialCell094.cell.b,Mean16FastPolynomialCell094.cell.total⟩,
  ⟨Mean16FastPolynomialCell095.cell.a,Mean16FastPolynomialCell095.cell.b,Mean16FastPolynomialCell095.cell.total⟩,
  ⟨Mean16FastPolynomialCell096.cell.a,Mean16FastPolynomialCell096.cell.b,Mean16FastPolynomialCell096.cell.total⟩,
  ⟨Mean16FastPolynomialCell097.cell.a,Mean16FastPolynomialCell097.cell.b,Mean16FastPolynomialCell097.cell.total⟩,
  ⟨Mean16FastPolynomialCell098.cell.a,Mean16FastPolynomialCell098.cell.b,Mean16FastPolynomialCell098.cell.total⟩,
  ⟨Mean16FastPolynomialCell099.cell.a,Mean16FastPolynomialCell099.cell.b,Mean16FastPolynomialCell099.cell.total⟩,
  ⟨Mean16FastPolynomialCell100.cell.a,Mean16FastPolynomialCell100.cell.b,Mean16FastPolynomialCell100.cell.total⟩,
  ⟨Mean16FastPolynomialCell101.cell.a,Mean16FastPolynomialCell101.cell.b,Mean16FastPolynomialCell101.cell.total⟩,
  ⟨Mean16FastPolynomialCell102.cell.a,Mean16FastPolynomialCell102.cell.b,Mean16FastPolynomialCell102.cell.total⟩,
  ⟨Mean16FastPolynomialCell103.cell.a,Mean16FastPolynomialCell103.cell.b,Mean16FastPolynomialCell103.cell.total⟩,
  ⟨Mean16FastPolynomialCell104.cell.a,Mean16FastPolynomialCell104.cell.b,Mean16FastPolynomialCell104.cell.total⟩,
  ⟨Mean16FastPolynomialCell105.cell.a,Mean16FastPolynomialCell105.cell.b,Mean16FastPolynomialCell105.cell.total⟩,
  ⟨Mean16FastPolynomialCell106.cell.a,Mean16FastPolynomialCell106.cell.b,Mean16FastPolynomialCell106.cell.total⟩,
  ⟨Mean16FastPolynomialCell107.cell.a,Mean16FastPolynomialCell107.cell.b,Mean16FastPolynomialCell107.cell.total⟩,
  ⟨Mean16FastPolynomialCell108.cell.a,Mean16FastPolynomialCell108.cell.b,Mean16FastPolynomialCell108.cell.total⟩,
  ⟨Mean16FastPolynomialCell109.cell.a,Mean16FastPolynomialCell109.cell.b,Mean16FastPolynomialCell109.cell.total⟩,
  ⟨Mean16FastPolynomialCell110.cell.a,Mean16FastPolynomialCell110.cell.b,Mean16FastPolynomialCell110.cell.total⟩,
  ⟨Mean16FastPolynomialCell111.cell.a,Mean16FastPolynomialCell111.cell.b,Mean16FastPolynomialCell111.cell.total⟩,
  ⟨Mean16FastPolynomialCell112.cell.a,Mean16FastPolynomialCell112.cell.b,Mean16FastPolynomialCell112.cell.total⟩,
  ⟨Mean16FastPolynomialCell113.cell.a,Mean16FastPolynomialCell113.cell.b,Mean16FastPolynomialCell113.cell.total⟩,
  ⟨Mean16FastPolynomialCell114.cell.a,Mean16FastPolynomialCell114.cell.b,Mean16FastPolynomialCell114.cell.total⟩,
  ⟨Mean16FastPolynomialCell115.cell.a,Mean16FastPolynomialCell115.cell.b,Mean16FastPolynomialCell115.cell.total⟩,
  ⟨Mean16FastPolynomialCell116.cell.a,Mean16FastPolynomialCell116.cell.b,Mean16FastPolynomialCell116.cell.total⟩,
  ⟨Mean16FastPolynomialCell117.cell.a,Mean16FastPolynomialCell117.cell.b,Mean16FastPolynomialCell117.cell.total⟩,
  ⟨Mean16FastPolynomialCell118.cell.a,Mean16FastPolynomialCell118.cell.b,Mean16FastPolynomialCell118.cell.total⟩,
  ⟨Mean16FastPolynomialCell119.cell.a,Mean16FastPolynomialCell119.cell.b,Mean16FastPolynomialCell119.cell.total⟩,
  ⟨Mean16FastPolynomialCell120.cell.a,Mean16FastPolynomialCell120.cell.b,Mean16FastPolynomialCell120.cell.total⟩,
  ⟨Mean16FastPolynomialCell121.cell.a,Mean16FastPolynomialCell121.cell.b,Mean16FastPolynomialCell121.cell.total⟩,
  ⟨Mean16FastPolynomialCell122.cell.a,Mean16FastPolynomialCell122.cell.b,Mean16FastPolynomialCell122.cell.total⟩,
  ⟨Mean16FastPolynomialCell123.cell.a,Mean16FastPolynomialCell123.cell.b,Mean16FastPolynomialCell123.cell.total⟩,
  ⟨Mean16FastPolynomialCell124.cell.a,Mean16FastPolynomialCell124.cell.b,Mean16FastPolynomialCell124.cell.total⟩,
  ⟨Mean16FastPolynomialCell125.cell.a,Mean16FastPolynomialCell125.cell.b,Mean16FastPolynomialCell125.cell.total⟩,
  ⟨Mean16FastPolynomialCell126.cell.a,Mean16FastPolynomialCell126.cell.b,Mean16FastPolynomialCell126.cell.total⟩,
  ⟨Mean16FastPolynomialCell127.cell.a,Mean16FastPolynomialCell127.cell.b,Mean16FastPolynomialCell127.cell.total⟩,
  ⟨Mean16FastPolynomialCell128.cell.a,Mean16FastPolynomialCell128.cell.b,Mean16FastPolynomialCell128.cell.total⟩,
  ⟨Mean16FastPolynomialCell129.cell.a,Mean16FastPolynomialCell129.cell.b,Mean16FastPolynomialCell129.cell.total⟩,
  ⟨Mean16FastPolynomialCell130.cell.a,Mean16FastPolynomialCell130.cell.b,Mean16FastPolynomialCell130.cell.total⟩,
  ⟨Mean16FastPolynomialCell131.cell.a,Mean16FastPolynomialCell131.cell.b,Mean16FastPolynomialCell131.cell.total⟩,
  ⟨Mean16FastPolynomialCell132.cell.a,Mean16FastPolynomialCell132.cell.b,Mean16FastPolynomialCell132.cell.total⟩,
  ⟨Mean16FastPolynomialCell133.cell.a,Mean16FastPolynomialCell133.cell.b,Mean16FastPolynomialCell133.cell.total⟩,
  ⟨Mean16FastPolynomialCell134.cell.a,Mean16FastPolynomialCell134.cell.b,Mean16FastPolynomialCell134.cell.total⟩,
  ⟨Mean16FastPolynomialCell135.cell.a,Mean16FastPolynomialCell135.cell.b,Mean16FastPolynomialCell135.cell.total⟩,
  ⟨Mean16FastPolynomialCell136.cell.a,Mean16FastPolynomialCell136.cell.b,Mean16FastPolynomialCell136.cell.total⟩,
  ⟨Mean16FastPolynomialCell137.cell.a,Mean16FastPolynomialCell137.cell.b,Mean16FastPolynomialCell137.cell.total⟩,
  ⟨Mean16FastPolynomialCell138.cell.a,Mean16FastPolynomialCell138.cell.b,Mean16FastPolynomialCell138.cell.total⟩,
  ⟨Mean16FastPolynomialCell139.cell.a,Mean16FastPolynomialCell139.cell.b,Mean16FastPolynomialCell139.cell.total⟩,
  ⟨Mean16FastPolynomialCell140.cell.a,Mean16FastPolynomialCell140.cell.b,Mean16FastPolynomialCell140.cell.total⟩,
  ⟨Mean16FastPolynomialCell141.cell.a,Mean16FastPolynomialCell141.cell.b,Mean16FastPolynomialCell141.cell.total⟩,
  ⟨Mean16FastPolynomialCell142.cell.a,Mean16FastPolynomialCell142.cell.b,Mean16FastPolynomialCell142.cell.total⟩,
  ⟨Mean16FastPolynomialCell143.cell.a,Mean16FastPolynomialCell143.cell.b,Mean16FastPolynomialCell143.cell.total⟩,
  ⟨Mean16FastPolynomialCell144.cell.a,Mean16FastPolynomialCell144.cell.b,Mean16FastPolynomialCell144.cell.total⟩,
  ⟨Mean16FastPolynomialCell145.cell.a,Mean16FastPolynomialCell145.cell.b,Mean16FastPolynomialCell145.cell.total⟩,
  ⟨Mean16FastPolynomialCell146.cell.a,Mean16FastPolynomialCell146.cell.b,Mean16FastPolynomialCell146.cell.total⟩,
  ⟨Mean16FastPolynomialCell147.cell.a,Mean16FastPolynomialCell147.cell.b,Mean16FastPolynomialCell147.cell.total⟩,
  ⟨Mean16FastPolynomialCell148.cell.a,Mean16FastPolynomialCell148.cell.b,Mean16FastPolynomialCell148.cell.total⟩,
  ⟨Mean16FastPolynomialCell149.cell.a,Mean16FastPolynomialCell149.cell.b,Mean16FastPolynomialCell149.cell.total⟩,
  ⟨Mean16FastPolynomialCell150.cell.a,Mean16FastPolynomialCell150.cell.b,Mean16FastPolynomialCell150.cell.total⟩,
  ⟨Mean16FastPolynomialCell151.cell.a,Mean16FastPolynomialCell151.cell.b,Mean16FastPolynomialCell151.cell.total⟩,
  ⟨Mean16FastPolynomialCell152.cell.a,Mean16FastPolynomialCell152.cell.b,Mean16FastPolynomialCell152.cell.total⟩,
  ⟨Mean16FastPolynomialCell153.cell.a,Mean16FastPolynomialCell153.cell.b,Mean16FastPolynomialCell153.cell.total⟩,
  ⟨Mean16FastPolynomialCell154.cell.a,Mean16FastPolynomialCell154.cell.b,Mean16FastPolynomialCell154.cell.total⟩,
  ⟨Mean16FastPolynomialCell155.cell.a,Mean16FastPolynomialCell155.cell.b,Mean16FastPolynomialCell155.cell.total⟩,
  ⟨Mean16FastPolynomialCell156.cell.a,Mean16FastPolynomialCell156.cell.b,Mean16FastPolynomialCell156.cell.total⟩,
  ⟨Mean16FastPolynomialCell157.cell.a,Mean16FastPolynomialCell157.cell.b,Mean16FastPolynomialCell157.cell.total⟩,
  ⟨Mean16FastPolynomialCell158.cell.a,Mean16FastPolynomialCell158.cell.b,Mean16FastPolynomialCell158.cell.total⟩,
  ⟨Mean16FastPolynomialCell159.cell.a,Mean16FastPolynomialCell159.cell.b,Mean16FastPolynomialCell159.cell.total⟩,
  ⟨Mean16FastPolynomialCell160.cell.a,Mean16FastPolynomialCell160.cell.b,Mean16FastPolynomialCell160.cell.total⟩,
  ⟨Mean16FastPolynomialCell161.cell.a,Mean16FastPolynomialCell161.cell.b,Mean16FastPolynomialCell161.cell.total⟩,
  ⟨Mean16FastPolynomialCell162.cell.a,Mean16FastPolynomialCell162.cell.b,Mean16FastPolynomialCell162.cell.total⟩,
  ⟨Mean16FastPolynomialCell163.cell.a,Mean16FastPolynomialCell163.cell.b,Mean16FastPolynomialCell163.cell.total⟩,
  ⟨Mean16FastPolynomialCell164.cell.a,Mean16FastPolynomialCell164.cell.b,Mean16FastPolynomialCell164.cell.total⟩,
  ⟨Mean16FastPolynomialCell165.cell.a,Mean16FastPolynomialCell165.cell.b,Mean16FastPolynomialCell165.cell.total⟩,
  ⟨Mean16FastPolynomialCell166.cell.a,Mean16FastPolynomialCell166.cell.b,Mean16FastPolynomialCell166.cell.total⟩,
  ⟨Mean16FastPolynomialCell167.cell.a,Mean16FastPolynomialCell167.cell.b,Mean16FastPolynomialCell167.cell.total⟩,
  ⟨Mean16FastPolynomialCell168.cell.a,Mean16FastPolynomialCell168.cell.b,Mean16FastPolynomialCell168.cell.total⟩,
  ⟨Mean16FastPolynomialCell169.cell.a,Mean16FastPolynomialCell169.cell.b,Mean16FastPolynomialCell169.cell.total⟩,
  ⟨Mean16FastPolynomialCell170.cell.a,Mean16FastPolynomialCell170.cell.b,Mean16FastPolynomialCell170.cell.total⟩,
  ⟨Mean16FastPolynomialCell171.cell.a,Mean16FastPolynomialCell171.cell.b,Mean16FastPolynomialCell171.cell.total⟩,
  ⟨Mean16FastPolynomialCell172.cell.a,Mean16FastPolynomialCell172.cell.b,Mean16FastPolynomialCell172.cell.total⟩,
  ⟨Mean16FastPolynomialCell173.cell.a,Mean16FastPolynomialCell173.cell.b,Mean16FastPolynomialCell173.cell.total⟩,
  ⟨Mean16FastPolynomialCell174.cell.a,Mean16FastPolynomialCell174.cell.b,Mean16FastPolynomialCell174.cell.total⟩,
  ⟨Mean16FastPolynomialCell175.cell.a,Mean16FastPolynomialCell175.cell.b,Mean16FastPolynomialCell175.cell.total⟩,
  ⟨Mean16FastPolynomialCell176.cell.a,Mean16FastPolynomialCell176.cell.b,Mean16FastPolynomialCell176.cell.total⟩,
  ⟨Mean16FastPolynomialCell177.cell.a,Mean16FastPolynomialCell177.cell.b,Mean16FastPolynomialCell177.cell.total⟩,
  ⟨Mean16FastPolynomialCell178.cell.a,Mean16FastPolynomialCell178.cell.b,Mean16FastPolynomialCell178.cell.total⟩,
  ⟨Mean16FastPolynomialCell179.cell.a,Mean16FastPolynomialCell179.cell.b,Mean16FastPolynomialCell179.cell.total⟩,
  ⟨Mean16FastPolynomialCell180.cell.a,Mean16FastPolynomialCell180.cell.b,Mean16FastPolynomialCell180.cell.total⟩,
  ⟨Mean16FastPolynomialCell181.cell.a,Mean16FastPolynomialCell181.cell.b,Mean16FastPolynomialCell181.cell.total⟩,
  ⟨Mean16FastPolynomialCell182.cell.a,Mean16FastPolynomialCell182.cell.b,Mean16FastPolynomialCell182.cell.total⟩,
  ⟨Mean16FastPolynomialCell183.cell.a,Mean16FastPolynomialCell183.cell.b,Mean16FastPolynomialCell183.cell.total⟩,
  ⟨Mean16FastPolynomialCell184.cell.a,Mean16FastPolynomialCell184.cell.b,Mean16FastPolynomialCell184.cell.total⟩,
  ⟨Mean16FastPolynomialCell185.cell.a,Mean16FastPolynomialCell185.cell.b,Mean16FastPolynomialCell185.cell.total⟩,
  ⟨Mean16FastPolynomialCell186.cell.a,Mean16FastPolynomialCell186.cell.b,Mean16FastPolynomialCell186.cell.total⟩,
  ⟨Mean16FastPolynomialCell187.cell.a,Mean16FastPolynomialCell187.cell.b,Mean16FastPolynomialCell187.cell.total⟩,
  ⟨Mean16FastPolynomialCell188.cell.a,Mean16FastPolynomialCell188.cell.b,Mean16FastPolynomialCell188.cell.total⟩,
  ⟨Mean16FastPolynomialCell189.cell.a,Mean16FastPolynomialCell189.cell.b,Mean16FastPolynomialCell189.cell.total⟩,
  ⟨Mean16FastPolynomialCell190.cell.a,Mean16FastPolynomialCell190.cell.b,Mean16FastPolynomialCell190.cell.total⟩,
  ⟨Mean16FastPolynomialCell191.cell.a,Mean16FastPolynomialCell191.cell.b,Mean16FastPolynomialCell191.cell.total⟩,
  ⟨Mean16FastPolynomialCell192.cell.a,Mean16FastPolynomialCell192.cell.b,Mean16FastPolynomialCell192.cell.total⟩,
  ⟨Mean16FastPolynomialCell193.cell.a,Mean16FastPolynomialCell193.cell.b,Mean16FastPolynomialCell193.cell.total⟩,
  ⟨Mean16FastPolynomialCell194.cell.a,Mean16FastPolynomialCell194.cell.b,Mean16FastPolynomialCell194.cell.total⟩,
  ⟨Mean16FastPolynomialCell195.cell.a,Mean16FastPolynomialCell195.cell.b,Mean16FastPolynomialCell195.cell.total⟩,
  ⟨Mean16FastPolynomialCell196.cell.a,Mean16FastPolynomialCell196.cell.b,Mean16FastPolynomialCell196.cell.total⟩,
  ⟨Mean16FastPolynomialCell197.cell.a,Mean16FastPolynomialCell197.cell.b,Mean16FastPolynomialCell197.cell.total⟩,
  ⟨Mean16FastPolynomialCell198.cell.a,Mean16FastPolynomialCell198.cell.b,Mean16FastPolynomialCell198.cell.total⟩,
  ⟨Mean16FastPolynomialCell199.cell.a,Mean16FastPolynomialCell199.cell.b,Mean16FastPolynomialCell199.cell.total⟩,
  ⟨Mean16FastPolynomialCell200.cell.a,Mean16FastPolynomialCell200.cell.b,Mean16FastPolynomialCell200.cell.total⟩,
  ⟨Mean16FastPolynomialCell201.cell.a,Mean16FastPolynomialCell201.cell.b,Mean16FastPolynomialCell201.cell.total⟩,
  ⟨Mean16FastPolynomialCell202.cell.a,Mean16FastPolynomialCell202.cell.b,Mean16FastPolynomialCell202.cell.total⟩,
  ⟨Mean16FastPolynomialCell203.cell.a,Mean16FastPolynomialCell203.cell.b,Mean16FastPolynomialCell203.cell.total⟩,
  ⟨Mean16FastPolynomialCell204.cell.a,Mean16FastPolynomialCell204.cell.b,Mean16FastPolynomialCell204.cell.total⟩,
  ⟨Mean16FastPolynomialCell205.cell.a,Mean16FastPolynomialCell205.cell.b,Mean16FastPolynomialCell205.cell.total⟩,
  ⟨Mean16FastPolynomialCell206.cell.a,Mean16FastPolynomialCell206.cell.b,Mean16FastPolynomialCell206.cell.total⟩,
  ⟨Mean16FastPolynomialCell207.cell.a,Mean16FastPolynomialCell207.cell.b,Mean16FastPolynomialCell207.cell.total⟩,
  ⟨Mean16FastPolynomialCell208.cell.a,Mean16FastPolynomialCell208.cell.b,Mean16FastPolynomialCell208.cell.total⟩,
  ⟨Mean16FastPolynomialCell209.cell.a,Mean16FastPolynomialCell209.cell.b,Mean16FastPolynomialCell209.cell.total⟩,
  ⟨Mean16FastPolynomialCell210.cell.a,Mean16FastPolynomialCell210.cell.b,Mean16FastPolynomialCell210.cell.total⟩,
  ⟨Mean16FastPolynomialCell211.cell.a,Mean16FastPolynomialCell211.cell.b,Mean16FastPolynomialCell211.cell.total⟩,
  ⟨Mean16FastPolynomialCell212.cell.a,Mean16FastPolynomialCell212.cell.b,Mean16FastPolynomialCell212.cell.total⟩,
  ⟨Mean16FastPolynomialCell213.cell.a,Mean16FastPolynomialCell213.cell.b,Mean16FastPolynomialCell213.cell.total⟩,
  ⟨Mean16FastPolynomialCell214.cell.a,Mean16FastPolynomialCell214.cell.b,Mean16FastPolynomialCell214.cell.total⟩,
  ⟨Mean16FastPolynomialCell215.cell.a,Mean16FastPolynomialCell215.cell.b,Mean16FastPolynomialCell215.cell.total⟩,
  ⟨Mean16FastPolynomialCell216.cell.a,Mean16FastPolynomialCell216.cell.b,Mean16FastPolynomialCell216.cell.total⟩,
  ⟨Mean16FastPolynomialCell217.cell.a,Mean16FastPolynomialCell217.cell.b,Mean16FastPolynomialCell217.cell.total⟩,
  ⟨Mean16FastPolynomialCell218.cell.a,Mean16FastPolynomialCell218.cell.b,Mean16FastPolynomialCell218.cell.total⟩,
  ⟨Mean16FastPolynomialCell219.cell.a,Mean16FastPolynomialCell219.cell.b,Mean16FastPolynomialCell219.cell.total⟩,
  ⟨Mean16FastPolynomialCell220.cell.a,Mean16FastPolynomialCell220.cell.b,Mean16FastPolynomialCell220.cell.total⟩,
  ⟨Mean16FastPolynomialCell221.cell.a,Mean16FastPolynomialCell221.cell.b,Mean16FastPolynomialCell221.cell.total⟩,
  ⟨Mean16FastPolynomialCell222.cell.a,Mean16FastPolynomialCell222.cell.b,Mean16FastPolynomialCell222.cell.total⟩,
  ⟨Mean16FastPolynomialCell223.cell.a,Mean16FastPolynomialCell223.cell.b,Mean16FastPolynomialCell223.cell.total⟩,
  ⟨Mean16FastPolynomialCell224.cell.a,Mean16FastPolynomialCell224.cell.b,Mean16FastPolynomialCell224.cell.total⟩,
  ⟨Mean16FastPolynomialCell225.cell.a,Mean16FastPolynomialCell225.cell.b,Mean16FastPolynomialCell225.cell.total⟩
]
def payment : ℚ := (13617434013499/250000000000000)

theorem chain_checked : check (1/16777216) 128 slices = true := by decide +kernel
theorem total_checked : total slices = payment := by decide +kernel

theorem actual_integral {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u : V) (hd : G.degree u = 1) :
    (payment : ℝ) ≤ ∫ y : ℝ in (1/16777216 : ℝ)..128,
      MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 0)
        (CoreQuotient.fused G u 0 0) (15/8) y := by
  let f := MixedGraphIntegral.logarithm (CoreQuotient.source G u 0 0) (CoreQuotient.fused G u 0 0) (15/8)
  have hf := ActualFusionIntegral.logarithm_integrable G u 0 0 (15/8)
  have hp : ∀ c ∈ slices, (c.payment : ℝ) ≤ ∫ y : ℝ in (c.a : ℝ)..(c.b : ℝ), f y := by
    intro c hc
    simp only [slices,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Mean16FastPolynomialCell000.actual_integral G u hd
    · exact Mean16FastPolynomialCell001.actual_integral G u hd
    · exact Mean16FastPolynomialCell002.actual_integral G u hd
    · exact Mean16FastPolynomialCell003.actual_integral G u hd
    · exact Mean16FastPolynomialCell004.actual_integral G u hd
    · exact Mean16FastPolynomialCell005.actual_integral G u hd
    · exact Mean16FastPolynomialCell006.actual_integral G u hd
    · exact Mean16FastPolynomialCell007.actual_integral G u hd
    · exact Mean16FastPolynomialCell008.actual_integral G u hd
    · exact Mean16FastPolynomialCell009.actual_integral G u hd
    · exact Mean16FastPolynomialCell010.actual_integral G u hd
    · exact Mean16FastPolynomialCell011.actual_integral G u hd
    · exact Mean16FastPolynomialCell012.actual_integral G u hd
    · exact Mean16FastPolynomialCell013.actual_integral G u hd
    · exact Mean16FastPolynomialCell014.actual_integral G u hd
    · exact Mean16FastPolynomialCell015.actual_integral G u hd
    · exact Mean16FastPolynomialCell016.actual_integral G u hd
    · exact Mean16FastPolynomialCell017.actual_integral G u hd
    · exact Mean16FastPolynomialCell018.actual_integral G u hd
    · exact Mean16FastPolynomialCell019.actual_integral G u hd
    · exact Mean16FastPolynomialCell020.actual_integral G u hd
    · exact Mean16FastPolynomialCell021.actual_integral G u hd
    · exact Mean16FastPolynomialCell022.actual_integral G u hd
    · exact Mean16FastPolynomialCell023.actual_integral G u hd
    · exact Mean16FastPolynomialCell024.actual_integral G u hd
    · exact Mean16FastPolynomialCell025.actual_integral G u hd
    · exact Mean16FastPolynomialCell026.actual_integral G u hd
    · exact Mean16FastPolynomialCell027.actual_integral G u hd
    · exact Mean16FastPolynomialCell028.actual_integral G u hd
    · exact Mean16FastPolynomialCell029.actual_integral G u hd
    · exact Mean16FastPolynomialCell030.actual_integral G u hd
    · exact Mean16FastPolynomialCell031.actual_integral G u hd
    · exact Mean16FastPolynomialCell032.actual_integral G u hd
    · exact Mean16FastPolynomialCell033.actual_integral G u hd
    · exact Mean16FastPolynomialCell034.actual_integral G u hd
    · exact Mean16FastPolynomialCell035.actual_integral G u hd
    · exact Mean16FastPolynomialCell036.actual_integral G u hd
    · exact Mean16FastPolynomialCell037.actual_integral G u hd
    · exact Mean16FastPolynomialCell038.actual_integral G u hd
    · exact Mean16FastPolynomialCell039.actual_integral G u hd
    · exact Mean16FastPolynomialCell040.actual_integral G u hd
    · exact Mean16FastPolynomialCell041.actual_integral G u hd
    · exact Mean16FastPolynomialCell042.actual_integral G u hd
    · exact Mean16FastPolynomialCell043.actual_integral G u hd
    · exact Mean16FastPolynomialCell044.actual_integral G u hd
    · exact Mean16FastPolynomialCell045.actual_integral G u hd
    · exact Mean16FastPolynomialCell046.actual_integral G u hd
    · exact Mean16FastPolynomialCell047.actual_integral G u hd
    · exact Mean16FastPolynomialCell048.actual_integral G u hd
    · exact Mean16FastPolynomialCell049.actual_integral G u hd
    · exact Mean16FastPolynomialCell050.actual_integral G u hd
    · exact Mean16FastPolynomialCell051.actual_integral G u hd
    · exact Mean16FastPolynomialCell052.actual_integral G u hd
    · exact Mean16FastPolynomialCell053.actual_integral G u hd
    · exact Mean16FastPolynomialCell054.actual_integral G u hd
    · exact Mean16FastPolynomialCell055.actual_integral G u hd
    · exact Mean16FastPolynomialCell056.actual_integral G u hd
    · exact Mean16FastPolynomialCell057.actual_integral G u hd
    · exact Mean16FastPolynomialCell058.actual_integral G u hd
    · exact Mean16FastPolynomialCell059.actual_integral G u hd
    · exact Mean16FastPolynomialCell060.actual_integral G u hd
    · exact Mean16FastPolynomialCell061.actual_integral G u hd
    · exact Mean16FastPolynomialCell062.actual_integral G u hd
    · exact Mean16FastPolynomialCell063.actual_integral G u hd
    · exact Mean16FastPolynomialCell064.actual_integral G u hd
    · exact Mean16FastPolynomialCell065.actual_integral G u hd
    · exact Mean16FastPolynomialCell066.actual_integral G u hd
    · exact Mean16FastPolynomialCell067.actual_integral G u hd
    · exact Mean16FastPolynomialCell068.actual_integral G u hd
    · exact Mean16FastPolynomialCell069.actual_integral G u hd
    · exact Mean16FastPolynomialCell070.actual_integral G u hd
    · exact Mean16FastPolynomialCell071.actual_integral G u hd
    · exact Mean16FastPolynomialCell072.actual_integral G u hd
    · exact Mean16FastPolynomialCell073.actual_integral G u hd
    · exact Mean16FastPolynomialCell074.actual_integral G u hd
    · exact Mean16FastPolynomialCell075.actual_integral G u hd
    · exact Mean16FastPolynomialCell076.actual_integral G u hd
    · exact Mean16FastPolynomialCell077.actual_integral G u hd
    · exact Mean16FastPolynomialCell078.actual_integral G u hd
    · exact Mean16FastPolynomialCell079.actual_integral G u hd
    · exact Mean16FastPolynomialCell080.actual_integral G u hd
    · exact Mean16FastPolynomialCell081.actual_integral G u hd
    · exact Mean16FastPolynomialCell082.actual_integral G u hd
    · exact Mean16FastPolynomialCell083.actual_integral G u hd
    · exact Mean16FastPolynomialCell084.actual_integral G u hd
    · exact Mean16FastPolynomialCell085.actual_integral G u hd
    · exact Mean16FastPolynomialCell086.actual_integral G u hd
    · exact Mean16FastPolynomialCell087.actual_integral G u hd
    · exact Mean16FastPolynomialCell088.actual_integral G u hd
    · exact Mean16FastPolynomialCell089.actual_integral G u hd
    · exact Mean16FastPolynomialCell090.actual_integral G u hd
    · exact Mean16FastPolynomialCell091.actual_integral G u hd
    · exact Mean16FastPolynomialCell092.actual_integral G u hd
    · exact Mean16FastPolynomialCell093.actual_integral G u hd
    · exact Mean16FastPolynomialCell094.actual_integral G u hd
    · exact Mean16FastPolynomialCell095.actual_integral G u hd
    · exact Mean16FastPolynomialCell096.actual_integral G u hd
    · exact Mean16FastPolynomialCell097.actual_integral G u hd
    · exact Mean16FastPolynomialCell098.actual_integral G u hd
    · exact Mean16FastPolynomialCell099.actual_integral G u hd
    · exact Mean16FastPolynomialCell100.actual_integral G u hd
    · exact Mean16FastPolynomialCell101.actual_integral G u hd
    · exact Mean16FastPolynomialCell102.actual_integral G u hd
    · exact Mean16FastPolynomialCell103.actual_integral G u hd
    · exact Mean16FastPolynomialCell104.actual_integral G u hd
    · exact Mean16FastPolynomialCell105.actual_integral G u hd
    · exact Mean16FastPolynomialCell106.actual_integral G u hd
    · exact Mean16FastPolynomialCell107.actual_integral G u hd
    · exact Mean16FastPolynomialCell108.actual_integral G u hd
    · exact Mean16FastPolynomialCell109.actual_integral G u hd
    · exact Mean16FastPolynomialCell110.actual_integral G u hd
    · exact Mean16FastPolynomialCell111.actual_integral G u hd
    · exact Mean16FastPolynomialCell112.actual_integral G u hd
    · exact Mean16FastPolynomialCell113.actual_integral G u hd
    · exact Mean16FastPolynomialCell114.actual_integral G u hd
    · exact Mean16FastPolynomialCell115.actual_integral G u hd
    · exact Mean16FastPolynomialCell116.actual_integral G u hd
    · exact Mean16FastPolynomialCell117.actual_integral G u hd
    · exact Mean16FastPolynomialCell118.actual_integral G u hd
    · exact Mean16FastPolynomialCell119.actual_integral G u hd
    · exact Mean16FastPolynomialCell120.actual_integral G u hd
    · exact Mean16FastPolynomialCell121.actual_integral G u hd
    · exact Mean16FastPolynomialCell122.actual_integral G u hd
    · exact Mean16FastPolynomialCell123.actual_integral G u hd
    · exact Mean16FastPolynomialCell124.actual_integral G u hd
    · exact Mean16FastPolynomialCell125.actual_integral G u hd
    · exact Mean16FastPolynomialCell126.actual_integral G u hd
    · exact Mean16FastPolynomialCell127.actual_integral G u hd
    · exact Mean16FastPolynomialCell128.actual_integral G u hd
    · exact Mean16FastPolynomialCell129.actual_integral G u hd
    · exact Mean16FastPolynomialCell130.actual_integral G u hd
    · exact Mean16FastPolynomialCell131.actual_integral G u hd
    · exact Mean16FastPolynomialCell132.actual_integral G u hd
    · exact Mean16FastPolynomialCell133.actual_integral G u hd
    · exact Mean16FastPolynomialCell134.actual_integral G u hd
    · exact Mean16FastPolynomialCell135.actual_integral G u hd
    · exact Mean16FastPolynomialCell136.actual_integral G u hd
    · exact Mean16FastPolynomialCell137.actual_integral G u hd
    · exact Mean16FastPolynomialCell138.actual_integral G u hd
    · exact Mean16FastPolynomialCell139.actual_integral G u hd
    · exact Mean16FastPolynomialCell140.actual_integral G u hd
    · exact Mean16FastPolynomialCell141.actual_integral G u hd
    · exact Mean16FastPolynomialCell142.actual_integral G u hd
    · exact Mean16FastPolynomialCell143.actual_integral G u hd
    · exact Mean16FastPolynomialCell144.actual_integral G u hd
    · exact Mean16FastPolynomialCell145.actual_integral G u hd
    · exact Mean16FastPolynomialCell146.actual_integral G u hd
    · exact Mean16FastPolynomialCell147.actual_integral G u hd
    · exact Mean16FastPolynomialCell148.actual_integral G u hd
    · exact Mean16FastPolynomialCell149.actual_integral G u hd
    · exact Mean16FastPolynomialCell150.actual_integral G u hd
    · exact Mean16FastPolynomialCell151.actual_integral G u hd
    · exact Mean16FastPolynomialCell152.actual_integral G u hd
    · exact Mean16FastPolynomialCell153.actual_integral G u hd
    · exact Mean16FastPolynomialCell154.actual_integral G u hd
    · exact Mean16FastPolynomialCell155.actual_integral G u hd
    · exact Mean16FastPolynomialCell156.actual_integral G u hd
    · exact Mean16FastPolynomialCell157.actual_integral G u hd
    · exact Mean16FastPolynomialCell158.actual_integral G u hd
    · exact Mean16FastPolynomialCell159.actual_integral G u hd
    · exact Mean16FastPolynomialCell160.actual_integral G u hd
    · exact Mean16FastPolynomialCell161.actual_integral G u hd
    · exact Mean16FastPolynomialCell162.actual_integral G u hd
    · exact Mean16FastPolynomialCell163.actual_integral G u hd
    · exact Mean16FastPolynomialCell164.actual_integral G u hd
    · exact Mean16FastPolynomialCell165.actual_integral G u hd
    · exact Mean16FastPolynomialCell166.actual_integral G u hd
    · exact Mean16FastPolynomialCell167.actual_integral G u hd
    · exact Mean16FastPolynomialCell168.actual_integral G u hd
    · exact Mean16FastPolynomialCell169.actual_integral G u hd
    · exact Mean16FastPolynomialCell170.actual_integral G u hd
    · exact Mean16FastPolynomialCell171.actual_integral G u hd
    · exact Mean16FastPolynomialCell172.actual_integral G u hd
    · exact Mean16FastPolynomialCell173.actual_integral G u hd
    · exact Mean16FastPolynomialCell174.actual_integral G u hd
    · exact Mean16FastPolynomialCell175.actual_integral G u hd
    · exact Mean16FastPolynomialCell176.actual_integral G u hd
    · exact Mean16FastPolynomialCell177.actual_integral G u hd
    · exact Mean16FastPolynomialCell178.actual_integral G u hd
    · exact Mean16FastPolynomialCell179.actual_integral G u hd
    · exact Mean16FastPolynomialCell180.actual_integral G u hd
    · exact Mean16FastPolynomialCell181.actual_integral G u hd
    · exact Mean16FastPolynomialCell182.actual_integral G u hd
    · exact Mean16FastPolynomialCell183.actual_integral G u hd
    · exact Mean16FastPolynomialCell184.actual_integral G u hd
    · exact Mean16FastPolynomialCell185.actual_integral G u hd
    · exact Mean16FastPolynomialCell186.actual_integral G u hd
    · exact Mean16FastPolynomialCell187.actual_integral G u hd
    · exact Mean16FastPolynomialCell188.actual_integral G u hd
    · exact Mean16FastPolynomialCell189.actual_integral G u hd
    · exact Mean16FastPolynomialCell190.actual_integral G u hd
    · exact Mean16FastPolynomialCell191.actual_integral G u hd
    · exact Mean16FastPolynomialCell192.actual_integral G u hd
    · exact Mean16FastPolynomialCell193.actual_integral G u hd
    · exact Mean16FastPolynomialCell194.actual_integral G u hd
    · exact Mean16FastPolynomialCell195.actual_integral G u hd
    · exact Mean16FastPolynomialCell196.actual_integral G u hd
    · exact Mean16FastPolynomialCell197.actual_integral G u hd
    · exact Mean16FastPolynomialCell198.actual_integral G u hd
    · exact Mean16FastPolynomialCell199.actual_integral G u hd
    · exact Mean16FastPolynomialCell200.actual_integral G u hd
    · exact Mean16FastPolynomialCell201.actual_integral G u hd
    · exact Mean16FastPolynomialCell202.actual_integral G u hd
    · exact Mean16FastPolynomialCell203.actual_integral G u hd
    · exact Mean16FastPolynomialCell204.actual_integral G u hd
    · exact Mean16FastPolynomialCell205.actual_integral G u hd
    · exact Mean16FastPolynomialCell206.actual_integral G u hd
    · exact Mean16FastPolynomialCell207.actual_integral G u hd
    · exact Mean16FastPolynomialCell208.actual_integral G u hd
    · exact Mean16FastPolynomialCell209.actual_integral G u hd
    · exact Mean16FastPolynomialCell210.actual_integral G u hd
    · exact Mean16FastPolynomialCell211.actual_integral G u hd
    · exact Mean16FastPolynomialCell212.actual_integral G u hd
    · exact Mean16FastPolynomialCell213.actual_integral G u hd
    · exact Mean16FastPolynomialCell214.actual_integral G u hd
    · exact Mean16FastPolynomialCell215.actual_integral G u hd
    · exact Mean16FastPolynomialCell216.actual_integral G u hd
    · exact Mean16FastPolynomialCell217.actual_integral G u hd
    · exact Mean16FastPolynomialCell218.actual_integral G u hd
    · exact Mean16FastPolynomialCell219.actual_integral G u hd
    · exact Mean16FastPolynomialCell220.actual_integral G u hd
    · exact Mean16FastPolynomialCell221.actual_integral G u hd
    · exact Mean16FastPolynomialCell222.actual_integral G u hd
    · exact Mean16FastPolynomialCell223.actual_integral G u hd
    · exact Mean16FastPolynomialCell224.actual_integral G u hd
    · exact Mean16FastPolynomialCell225.actual_integral G u hd
  have h := RationalIntegralPartition.integral_lower f hf (1/16777216) 128 slices
    (by norm_num) chain_checked hp
  rw [total_checked] at h
  exact h

#print axioms chain_checked
#print axioms total_checked
#print axioms actual_integral
end
end Gebendorfer.RadenkovicGutman.Mean16FinitePayment
