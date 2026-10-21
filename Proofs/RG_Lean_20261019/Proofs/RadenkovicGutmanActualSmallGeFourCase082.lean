/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons04
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core082 : Family 7 := level7.get ⟨106,by decide⟩
def sourceMap082 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 7 0 2 v)
def fusedMap082 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap082_checked : acceptsGraphIso
    (source (graph core082) (root 7) 0 2) SmallGeFourSpectrum132.graph
      sourceMap082=true := by decide +kernel
theorem fusedMap082_checked : acceptsGraphIso
    (fused (graph core082) (root 7) 0 2) SmallGeFourSpectrum133.graph
      fusedMap082=true := by decide +kernel
theorem certified082 : Certified (graph core082) (root 7) 0 2 :=
  of_native_maps core082 SmallGeFourSpectrum132.graph SmallGeFourSpectrum133.graph
    sourceMap082 fusedMap082 sourceMap082_checked fusedMap082_checked
    SmallGeFourComparisons.comparison082
#print axioms sourceMap082_checked
#print axioms fusedMap082_checked
#print axioms certified082
def sourceMap082swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,8] (sourceLabel 7 2 0 v)
def fusedMap082swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap082swap_checked : acceptsGraphIso
    (source (graph core082) (root 7) 2 0) SmallGeFourSpectrum132.graph
      sourceMap082swap=true := by decide +kernel
theorem fusedMap082swap_checked : acceptsGraphIso
    (fused (graph core082) (root 7) 2 0) SmallGeFourSpectrum133.graph
      fusedMap082swap=true := by decide +kernel
theorem certified082swap : Certified (graph core082) (root 7) 2 0 :=
  of_native_maps core082 SmallGeFourSpectrum132.graph SmallGeFourSpectrum133.graph
    sourceMap082swap fusedMap082swap sourceMap082swap_checked fusedMap082swap_checked
    SmallGeFourComparisons.comparison082
#print axioms sourceMap082swap_checked
#print axioms fusedMap082swap_checked
#print axioms certified082swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
