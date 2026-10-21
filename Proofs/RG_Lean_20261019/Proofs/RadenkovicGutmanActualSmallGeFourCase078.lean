/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons04
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core078 : Family 7 := level7.get ⟨99,by decide⟩
def sourceMap078 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,7,8,9,10,11,4,5,6] (sourceLabel 7 0 2 v)
def fusedMap078 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap078_checked : acceptsGraphIso
    (source (graph core078) (root 7) 0 2) SmallGeFourSpectrum196.graph
      sourceMap078=true := by decide +kernel
theorem fusedMap078_checked : acceptsGraphIso
    (fused (graph core078) (root 7) 0 2) SmallGeFourSpectrum108.graph
      fusedMap078=true := by decide +kernel
theorem certified078 : Certified (graph core078) (root 7) 0 2 :=
  of_native_maps core078 SmallGeFourSpectrum196.graph SmallGeFourSpectrum108.graph
    sourceMap078 fusedMap078 sourceMap078_checked fusedMap078_checked
    SmallGeFourComparisons.comparison078
#print axioms sourceMap078_checked
#print axioms fusedMap078_checked
#print axioms certified078
def sourceMap078swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,7,8,9,10,4,5,6,11] (sourceLabel 7 2 0 v)
def fusedMap078swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap078swap_checked : acceptsGraphIso
    (source (graph core078) (root 7) 2 0) SmallGeFourSpectrum196.graph
      sourceMap078swap=true := by decide +kernel
theorem fusedMap078swap_checked : acceptsGraphIso
    (fused (graph core078) (root 7) 2 0) SmallGeFourSpectrum108.graph
      fusedMap078swap=true := by decide +kernel
theorem certified078swap : Certified (graph core078) (root 7) 2 0 :=
  of_native_maps core078 SmallGeFourSpectrum196.graph SmallGeFourSpectrum108.graph
    sourceMap078swap fusedMap078swap sourceMap078swap_checked fusedMap078swap_checked
    SmallGeFourComparisons.comparison078
#print axioms sourceMap078swap_checked
#print axioms fusedMap078swap_checked
#print axioms certified078swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
