/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum370
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum371
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum372
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum373
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum376
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum377
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum379
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum380
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum381
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum382
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum384
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum385
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum387
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum388
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum389
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum390
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum391
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum392
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum393
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum394
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum395
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum396
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum397
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum420
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum449
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum453
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum456
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum471
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum475
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum478
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum479
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum480
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum483
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum486
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum489
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum490
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum494
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum496
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum497
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum498
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum499
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum857
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum858
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum859
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum860
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum867
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum870
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum876
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum879
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum884
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum887
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum891
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum894
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum898
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum899
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum907
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum908
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum912
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum915
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum919
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum922
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum926
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum927
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum929
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum932
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum933
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum935
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum936
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum937
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum938
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum939
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum940
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum941
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum942
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum943
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum944
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum951
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum956
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum961
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum965
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum966
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum971
import Proofs.RadenkovicGutmanDegreeOneSmallSpectrum974
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
set_option maxHeartbeats 0
theorem comparison1200 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum857.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum936.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum936.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum857.actual_graph_bounds.2
  linarith
#print axioms comparison1200
theorem comparison1201 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum392.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum376.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum376.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum392.actual_graph_bounds.2
  linarith
#print axioms comparison1201
theorem comparison1202 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum858.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum940.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum940.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum858.actual_graph_bounds.2
  linarith
#print axioms comparison1202
theorem comparison1203 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum396.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum377.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum377.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum396.actual_graph_bounds.2
  linarith
#print axioms comparison1203
theorem comparison1204 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum859.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum943.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum943.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum859.actual_graph_bounds.2
  linarith
#print axioms comparison1204
theorem comparison1205 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum397.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum373.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum373.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum397.actual_graph_bounds.2
  linarith
#print axioms comparison1205
theorem comparison1206 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum860.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum944.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum944.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum860.actual_graph_bounds.2
  linarith
#print axioms comparison1206
theorem comparison1207 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum396.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum372.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum372.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum396.actual_graph_bounds.2
  linarith
#print axioms comparison1207
theorem comparison1208 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum860.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum935.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum935.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum860.actual_graph_bounds.2
  linarith
#print axioms comparison1208
theorem comparison1209 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum392.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum371.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum371.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum392.actual_graph_bounds.2
  linarith
#print axioms comparison1209
theorem comparison1210 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum859.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum929.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum929.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum859.actual_graph_bounds.2
  linarith
#print axioms comparison1210
theorem comparison1211 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum370.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum420.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum420.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum370.actual_graph_bounds.2
  linarith
#print axioms comparison1211
theorem comparison1212 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum870.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum867.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum867.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum870.actual_graph_bounds.2
  linarith
#print axioms comparison1212
theorem comparison1213 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum371.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum449.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum449.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum371.actual_graph_bounds.2
  linarith
#print axioms comparison1213
theorem comparison1214 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum879.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum876.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum876.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum879.actual_graph_bounds.2
  linarith
#print axioms comparison1214
theorem comparison1215 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum372.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum471.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum471.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum372.actual_graph_bounds.2
  linarith
#print axioms comparison1215
theorem comparison1216 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum887.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum884.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum884.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum887.actual_graph_bounds.2
  linarith
#print axioms comparison1216
theorem comparison1217 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum373.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum480.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum480.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum373.actual_graph_bounds.2
  linarith
#print axioms comparison1217
theorem comparison1218 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum894.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum891.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum891.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum894.actual_graph_bounds.2
  linarith
#print axioms comparison1218
theorem comparison1219 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum377.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum471.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum471.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum377.actual_graph_bounds.2
  linarith
#print axioms comparison1219
theorem comparison1220 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum908.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum899.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum899.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum908.actual_graph_bounds.2
  linarith
#print axioms comparison1220
theorem comparison1221 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum376.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum449.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum449.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum376.actual_graph_bounds.2
  linarith
#print axioms comparison1221
theorem comparison1222 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum907.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum898.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum898.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum907.actual_graph_bounds.2
  linarith
#print axioms comparison1222
theorem comparison1223 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum379.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum483.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum483.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum379.actual_graph_bounds.2
  linarith
#print axioms comparison1223
theorem comparison1224 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum915.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum912.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum912.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum915.actual_graph_bounds.2
  linarith
#print axioms comparison1224
theorem comparison1225 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum380.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum486.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum486.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum380.actual_graph_bounds.2
  linarith
#print axioms comparison1225
theorem comparison1226 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum922.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum919.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum919.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum922.actual_graph_bounds.2
  linarith
#print axioms comparison1226
theorem comparison1227 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum381.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum489.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum489.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum381.actual_graph_bounds.2
  linarith
#print axioms comparison1227
theorem comparison1228 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum929.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum926.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum926.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum929.actual_graph_bounds.2
  linarith
#print axioms comparison1228
theorem comparison1229 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum382.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum490.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum490.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum382.actual_graph_bounds.2
  linarith
#print axioms comparison1229
theorem comparison1230 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum935.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum932.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum932.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum935.actual_graph_bounds.2
  linarith
#print axioms comparison1230
theorem comparison1231 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum385.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum475.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum475.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum385.actual_graph_bounds.2
  linarith
#print axioms comparison1231
theorem comparison1232 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum944.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum932.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum932.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum944.actual_graph_bounds.2
  linarith
#print axioms comparison1232
theorem comparison1233 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum384.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum453.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum453.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum384.actual_graph_bounds.2
  linarith
#print axioms comparison1233
theorem comparison1234 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum943.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum926.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum926.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum943.actual_graph_bounds.2
  linarith
#print axioms comparison1234
theorem comparison1235 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum387.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum494.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum494.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum387.actual_graph_bounds.2
  linarith
#print axioms comparison1235
theorem comparison1236 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum951.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum937.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum937.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum951.actual_graph_bounds.2
  linarith
#print axioms comparison1236
theorem comparison1237 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum388.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum496.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum496.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum388.actual_graph_bounds.2
  linarith
#print axioms comparison1237
theorem comparison1238 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum956.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum938.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum938.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum956.actual_graph_bounds.2
  linarith
#print axioms comparison1238
theorem comparison1239 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum389.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum497.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum497.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum389.actual_graph_bounds.2
  linarith
#print axioms comparison1239
theorem comparison1240 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum961.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum939.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum939.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum961.actual_graph_bounds.2
  linarith
#print axioms comparison1240
theorem comparison1241 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum391.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum478.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum478.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum391.actual_graph_bounds.2
  linarith
#print axioms comparison1241
theorem comparison1242 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum966.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum933.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum933.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum966.actual_graph_bounds.2
  linarith
#print axioms comparison1242
theorem comparison1243 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum390.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum456.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum456.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum390.actual_graph_bounds.2
  linarith
#print axioms comparison1243
theorem comparison1244 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum965.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum927.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum927.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum965.actual_graph_bounds.2
  linarith
#print axioms comparison1244
theorem comparison1245 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum393.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum498.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum498.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum393.actual_graph_bounds.2
  linarith
#print axioms comparison1245
theorem comparison1246 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum971.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum941.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum941.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum971.actual_graph_bounds.2
  linarith
#print axioms comparison1246
theorem comparison1247 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum394.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum499.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum499.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum394.actual_graph_bounds.2
  linarith
#print axioms comparison1247
theorem comparison1248 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum974.graph) (2-2/13) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum942.graph) (2-2/13) := by
  have hs := DegreeOneSmallSpectrum942.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum974.actual_graph_bounds.2
  linarith
#print axioms comparison1248
theorem comparison1249 :
    stopLoss (laplacianSpectrum DegreeOneSmallSpectrum395.graph) (2-2/12) <
      stopLoss (laplacianSpectrum DegreeOneSmallSpectrum479.graph) (2-2/12) := by
  have hs := DegreeOneSmallSpectrum479.actual_graph_bounds.1
  have ht := DegreeOneSmallSpectrum395.actual_graph_bounds.2
  linarith
#print axioms comparison1249
end Gebendorfer.RadenkovicGutman.DegreeOneSmallComparisons
