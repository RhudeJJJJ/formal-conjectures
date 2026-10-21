/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanSmallGeFourSpectrum000
import Proofs.RadenkovicGutmanSmallGeFourSpectrum001
import Proofs.RadenkovicGutmanSmallGeFourSpectrum002
import Proofs.RadenkovicGutmanSmallGeFourSpectrum003
import Proofs.RadenkovicGutmanSmallGeFourSpectrum004
import Proofs.RadenkovicGutmanSmallGeFourSpectrum006
import Proofs.RadenkovicGutmanSmallGeFourSpectrum007
import Proofs.RadenkovicGutmanSmallGeFourSpectrum010
import Proofs.RadenkovicGutmanSmallGeFourSpectrum013
import Proofs.RadenkovicGutmanSmallGeFourSpectrum015
import Proofs.RadenkovicGutmanSmallGeFourSpectrum016
import Proofs.RadenkovicGutmanSmallGeFourSpectrum020
import Proofs.RadenkovicGutmanSmallGeFourSpectrum022
import Proofs.RadenkovicGutmanSmallGeFourSpectrum037
import Proofs.RadenkovicGutmanSmallGeFourSpectrum038
import Proofs.RadenkovicGutmanSmallGeFourSpectrum044
import Proofs.RadenkovicGutmanSmallGeFourSpectrum062
import Proofs.RadenkovicGutmanSmallGeFourSpectrum068
import Proofs.RadenkovicGutmanSmallGeFourSpectrum093
import Proofs.RadenkovicGutmanSmallGeFourSpectrum094
import Proofs.RadenkovicGutmanSmallGeFourSpectrum100
import Proofs.RadenkovicGutmanSmallGeFourSpectrum104
import Proofs.RadenkovicGutmanSmallGeFourSpectrum108
namespace Gebendorfer.RadenkovicGutman.SmallGeFourComparisons
set_option maxHeartbeats 0
theorem comparison000 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum000.graph) (2-2/7) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum001.graph) (2-2/7) := by
  have hs := SmallGeFourSpectrum001.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum000.actual_graph_bounds.2
  linarith
#print axioms comparison000
theorem comparison001 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum003.graph) (2-2/8) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum002.graph) (2-2/8) := by
  have hs := SmallGeFourSpectrum002.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum003.actual_graph_bounds.2
  linarith
#print axioms comparison001
theorem comparison002 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum006.graph) (2-2/9) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum010.graph) (2-2/9) := by
  have hs := SmallGeFourSpectrum010.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum006.actual_graph_bounds.2
  linarith
#print axioms comparison002
theorem comparison003 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum016.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum015.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum015.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum016.actual_graph_bounds.2
  linarith
#print axioms comparison003
theorem comparison004 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum037.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum044.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum044.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum037.actual_graph_bounds.2
  linarith
#print axioms comparison004
theorem comparison005 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum094.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum093.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum093.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum094.actual_graph_bounds.2
  linarith
#print axioms comparison005
theorem comparison006 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum006.graph) (2-2/9) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum013.graph) (2-2/9) := by
  have hs := SmallGeFourSpectrum013.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum006.actual_graph_bounds.2
  linarith
#print axioms comparison006
theorem comparison007 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum016.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum020.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum020.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum016.actual_graph_bounds.2
  linarith
#print axioms comparison007
theorem comparison008 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum037.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum062.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum062.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum037.actual_graph_bounds.2
  linarith
#print axioms comparison008
theorem comparison009 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum094.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum100.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum100.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum094.actual_graph_bounds.2
  linarith
#print axioms comparison009
theorem comparison010 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum037.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum068.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum068.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum037.actual_graph_bounds.2
  linarith
#print axioms comparison010
theorem comparison011 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum094.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum108.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum108.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum094.actual_graph_bounds.2
  linarith
#print axioms comparison011
theorem comparison012 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum004.graph) (2-2/8) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum002.graph) (2-2/8) := by
  have hs := SmallGeFourSpectrum002.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum004.actual_graph_bounds.2
  linarith
#print axioms comparison012
theorem comparison013 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum007.graph) (2-2/9) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum013.graph) (2-2/9) := by
  have hs := SmallGeFourSpectrum013.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum007.actual_graph_bounds.2
  linarith
#print axioms comparison013
theorem comparison014 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum022.graph) (2-2/10) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum020.graph) (2-2/10) := by
  have hs := SmallGeFourSpectrum020.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum022.actual_graph_bounds.2
  linarith
#print axioms comparison014
theorem comparison015 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum038.graph) (2-2/11) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum062.graph) (2-2/11) := by
  have hs := SmallGeFourSpectrum062.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum038.actual_graph_bounds.2
  linarith
#print axioms comparison015
theorem comparison016 :
    stopLoss (laplacianSpectrum SmallGeFourSpectrum104.graph) (2-2/12) <
      stopLoss (laplacianSpectrum SmallGeFourSpectrum100.graph) (2-2/12) := by
  have hs := SmallGeFourSpectrum100.actual_graph_bounds.1
  have ht := SmallGeFourSpectrum104.actual_graph_bounds.2
  linarith
#print axioms comparison016
end Gebendorfer.RadenkovicGutman.SmallGeFourComparisons
