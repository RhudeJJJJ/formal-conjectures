/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons04
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core070 : Family 7 := level7.get ⟨93,by decide⟩
def sourceMap070 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,8,9,10,11,5,6,7] (sourceLabel 7 0 2 v)
def fusedMap070 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap070_checked : acceptsGraphIso
    (source (graph core070) (root 7) 0 2) SmallGeFourSpectrum191.graph
      sourceMap070=true := by decide +kernel
theorem fusedMap070_checked : acceptsGraphIso
    (fused (graph core070) (root 7) 0 2) SmallGeFourSpectrum105.graph
      fusedMap070=true := by decide +kernel
theorem certified070 : Certified (graph core070) (root 7) 0 2 :=
  of_native_maps core070 SmallGeFourSpectrum191.graph SmallGeFourSpectrum105.graph
    sourceMap070 fusedMap070 sourceMap070_checked fusedMap070_checked
    SmallGeFourComparisons.comparison070
#print axioms sourceMap070_checked
#print axioms fusedMap070_checked
#print axioms certified070
def sourceMap070swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,8,9,10,5,6,7,11] (sourceLabel 7 2 0 v)
def fusedMap070swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap070swap_checked : acceptsGraphIso
    (source (graph core070) (root 7) 2 0) SmallGeFourSpectrum191.graph
      sourceMap070swap=true := by decide +kernel
theorem fusedMap070swap_checked : acceptsGraphIso
    (fused (graph core070) (root 7) 2 0) SmallGeFourSpectrum105.graph
      fusedMap070swap=true := by decide +kernel
theorem certified070swap : Certified (graph core070) (root 7) 2 0 :=
  of_native_maps core070 SmallGeFourSpectrum191.graph SmallGeFourSpectrum105.graph
    sourceMap070swap fusedMap070swap sourceMap070swap_checked fusedMap070swap_checked
    SmallGeFourComparisons.comparison070
#print axioms sourceMap070swap_checked
#print axioms fusedMap070swap_checked
#print axioms certified070swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
