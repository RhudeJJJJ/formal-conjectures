/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons03
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core066 : Family 7 := level7.get ⟨80,by decide⟩
def sourceMap066 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,8,9,10,11,5,6,7] (sourceLabel 7 0 2 v)
def fusedMap066 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap066_checked : acceptsGraphIso
    (source (graph core066) (root 7) 0 2) SmallGeFourSpectrum162.graph
      sourceMap066=true := by decide +kernel
theorem fusedMap066_checked : acceptsGraphIso
    (fused (graph core066) (root 7) 0 2) SmallGeFourSpectrum096.graph
      fusedMap066=true := by decide +kernel
theorem certified066 : Certified (graph core066) (root 7) 0 2 :=
  of_native_maps core066 SmallGeFourSpectrum162.graph SmallGeFourSpectrum096.graph
    sourceMap066 fusedMap066 sourceMap066_checked fusedMap066_checked
    SmallGeFourComparisons.comparison066
#print axioms sourceMap066_checked
#print axioms fusedMap066_checked
#print axioms certified066
def sourceMap066swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,8,9,10,5,6,7,11] (sourceLabel 7 2 0 v)
def fusedMap066swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap066swap_checked : acceptsGraphIso
    (source (graph core066) (root 7) 2 0) SmallGeFourSpectrum162.graph
      sourceMap066swap=true := by decide +kernel
theorem fusedMap066swap_checked : acceptsGraphIso
    (fused (graph core066) (root 7) 2 0) SmallGeFourSpectrum096.graph
      fusedMap066swap=true := by decide +kernel
theorem certified066swap : Certified (graph core066) (root 7) 2 0 :=
  of_native_maps core066 SmallGeFourSpectrum162.graph SmallGeFourSpectrum096.graph
    sourceMap066swap fusedMap066swap sourceMap066swap_checked fusedMap066swap_checked
    SmallGeFourComparisons.comparison066
#print axioms sourceMap066swap_checked
#print axioms fusedMap066swap_checked
#print axioms certified066swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
