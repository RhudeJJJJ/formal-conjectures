/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons09
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core168 : Family 8 := level8.get ⟨285,by decide⟩
def sourceMap168 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap168 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap168_checked : acceptsGraphIso
    (source (graph core168) (root 8) 0 0) SmallGeFourSpectrum092.graph
      sourceMap168=true := by decide +kernel
theorem fusedMap168_checked : acceptsGraphIso
    (fused (graph core168) (root 8) 0 0) SmallGeFourSpectrum069.graph
      fusedMap168=true := by decide +kernel
theorem certified168 : Certified (graph core168) (root 8) 0 0 :=
  of_native_maps core168 SmallGeFourSpectrum092.graph SmallGeFourSpectrum069.graph
    sourceMap168 fusedMap168 sourceMap168_checked fusedMap168_checked
    SmallGeFourComparisons.comparison168
#print axioms sourceMap168_checked
#print axioms fusedMap168_checked
#print axioms certified168
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
