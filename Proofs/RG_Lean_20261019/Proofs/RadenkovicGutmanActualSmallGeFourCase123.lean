/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons07
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core123 : Family 8 := level8.get ⟨221,by decide⟩
def sourceMap123 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,6,7] (sourceLabel 8 0 1 v)
def fusedMap123 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,9,10,11,6,7,8] (fusedLabel 8 0 1 v)
theorem sourceMap123_checked : acceptsGraphIso
    (source (graph core123) (root 8) 0 1) SmallGeFourSpectrum152.graph
      sourceMap123=true := by decide +kernel
theorem fusedMap123_checked : acceptsGraphIso
    (fused (graph core123) (root 8) 0 1) SmallGeFourSpectrum154.graph
      fusedMap123=true := by decide +kernel
theorem certified123 : Certified (graph core123) (root 8) 0 1 :=
  of_native_maps core123 SmallGeFourSpectrum152.graph SmallGeFourSpectrum154.graph
    sourceMap123 fusedMap123 sourceMap123_checked fusedMap123_checked
    SmallGeFourComparisons.comparison123
#print axioms sourceMap123_checked
#print axioms fusedMap123_checked
#print axioms certified123
def sourceMap123swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,8,9,10,6,7,11] (sourceLabel 8 1 0 v)
def fusedMap123swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,9,10,11,6,7,8] (fusedLabel 8 1 0 v)
theorem sourceMap123swap_checked : acceptsGraphIso
    (source (graph core123) (root 8) 1 0) SmallGeFourSpectrum152.graph
      sourceMap123swap=true := by decide +kernel
theorem fusedMap123swap_checked : acceptsGraphIso
    (fused (graph core123) (root 8) 1 0) SmallGeFourSpectrum154.graph
      fusedMap123swap=true := by decide +kernel
theorem certified123swap : Certified (graph core123) (root 8) 1 0 :=
  of_native_maps core123 SmallGeFourSpectrum152.graph SmallGeFourSpectrum154.graph
    sourceMap123swap fusedMap123swap sourceMap123swap_checked fusedMap123swap_checked
    SmallGeFourComparisons.comparison123
#print axioms sourceMap123swap_checked
#print axioms fusedMap123swap_checked
#print axioms certified123swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
