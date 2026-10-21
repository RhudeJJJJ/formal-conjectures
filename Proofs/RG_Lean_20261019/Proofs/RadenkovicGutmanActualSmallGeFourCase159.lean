/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons09
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core159 : Family 8 := level8.get ⟨280,by decide⟩
def sourceMap159 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,6,7,8,9,10,11,4,5] (sourceLabel 8 0 1 v)
def fusedMap159 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap159_checked : acceptsGraphIso
    (source (graph core159) (root 8) 0 1) SmallGeFourSpectrum228.graph
      sourceMap159=true := by decide +kernel
theorem fusedMap159_checked : acceptsGraphIso
    (fused (graph core159) (root 8) 0 1) SmallGeFourSpectrum146.graph
      fusedMap159=true := by decide +kernel
theorem certified159 : Certified (graph core159) (root 8) 0 1 :=
  of_native_maps core159 SmallGeFourSpectrum228.graph SmallGeFourSpectrum146.graph
    sourceMap159 fusedMap159 sourceMap159_checked fusedMap159_checked
    SmallGeFourComparisons.comparison159
#print axioms sourceMap159_checked
#print axioms fusedMap159_checked
#print axioms certified159
def sourceMap159swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,6,7,8,9,10,4,5,11] (sourceLabel 8 1 0 v)
def fusedMap159swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap159swap_checked : acceptsGraphIso
    (source (graph core159) (root 8) 1 0) SmallGeFourSpectrum228.graph
      sourceMap159swap=true := by decide +kernel
theorem fusedMap159swap_checked : acceptsGraphIso
    (fused (graph core159) (root 8) 1 0) SmallGeFourSpectrum146.graph
      fusedMap159swap=true := by decide +kernel
theorem certified159swap : Certified (graph core159) (root 8) 1 0 :=
  of_native_maps core159 SmallGeFourSpectrum228.graph SmallGeFourSpectrum146.graph
    sourceMap159swap fusedMap159swap sourceMap159swap_checked fusedMap159swap_checked
    SmallGeFourComparisons.comparison159
#print axioms sourceMap159swap_checked
#print axioms fusedMap159swap_checked
#print axioms certified159swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
