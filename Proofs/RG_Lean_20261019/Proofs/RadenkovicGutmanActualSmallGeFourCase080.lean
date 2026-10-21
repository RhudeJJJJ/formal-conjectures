/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons04
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core080 : Family 7 := level7.get ⟨106,by decide⟩
def sourceMap080 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,6,7,8,9,1,2,3,4,5] (sourceLabel 7 0 0 v)
def fusedMap080 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,3,4,7,8,9,5,6] (fusedLabel 7 0 0 v)
theorem sourceMap080_checked : acceptsGraphIso
    (source (graph core080) (root 7) 0 0) SmallGeFourSpectrum027.graph
      sourceMap080=true := by decide +kernel
theorem fusedMap080_checked : acceptsGraphIso
    (fused (graph core080) (root 7) 0 0) SmallGeFourSpectrum030.graph
      fusedMap080=true := by decide +kernel
theorem certified080 : Certified (graph core080) (root 7) 0 0 :=
  of_native_maps core080 SmallGeFourSpectrum027.graph SmallGeFourSpectrum030.graph
    sourceMap080 fusedMap080 sourceMap080_checked fusedMap080_checked
    SmallGeFourComparisons.comparison080
#print axioms sourceMap080_checked
#print axioms fusedMap080_checked
#print axioms certified080
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
