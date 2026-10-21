/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons05
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core089 : Family 7 := level7.get ⟨110,by decide⟩
def sourceMap089 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,6,7,8,9,10,4,5] (sourceLabel 7 0 1 v)
def fusedMap089 : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 0 1 v)
theorem sourceMap089_checked : acceptsGraphIso
    (source (graph core089) (root 7) 0 1) SmallGeFourSpectrum087.graph
      sourceMap089=true := by decide +kernel
theorem fusedMap089_checked : acceptsGraphIso
    (fused (graph core089) (root 7) 0 1) SmallGeFourSpectrum048.graph
      fusedMap089=true := by decide +kernel
theorem certified089 : Certified (graph core089) (root 7) 0 1 :=
  of_native_maps core089 SmallGeFourSpectrum087.graph SmallGeFourSpectrum048.graph
    sourceMap089 fusedMap089 sourceMap089_checked fusedMap089_checked
    SmallGeFourComparisons.comparison089
#print axioms sourceMap089_checked
#print axioms fusedMap089_checked
#print axioms certified089
def sourceMap089swap : (Vertices 7 ⊕ Fin 2 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,6,7,8,9,4,5,10] (sourceLabel 7 1 0 v)
def fusedMap089swap : (Vertices 7 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 7 1 0 v)
theorem sourceMap089swap_checked : acceptsGraphIso
    (source (graph core089) (root 7) 1 0) SmallGeFourSpectrum087.graph
      sourceMap089swap=true := by decide +kernel
theorem fusedMap089swap_checked : acceptsGraphIso
    (fused (graph core089) (root 7) 1 0) SmallGeFourSpectrum048.graph
      fusedMap089swap=true := by decide +kernel
theorem certified089swap : Certified (graph core089) (root 7) 1 0 :=
  of_native_maps core089 SmallGeFourSpectrum087.graph SmallGeFourSpectrum048.graph
    sourceMap089swap fusedMap089swap sourceMap089swap_checked fusedMap089swap_checked
    SmallGeFourComparisons.comparison089
#print axioms sourceMap089swap_checked
#print axioms fusedMap089swap_checked
#print axioms certified089swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
