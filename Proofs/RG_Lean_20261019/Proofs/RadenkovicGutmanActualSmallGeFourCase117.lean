/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons06
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core117 : Family 8 := level8.get ⟨186,by decide⟩
def sourceMap117 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,9,10,11,2,3,6,7,8,4,5] (sourceLabel 8 0 1 v)
def fusedMap117 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,8,9,10,11,4,5,6,7,1,2,3] (fusedLabel 8 0 1 v)
theorem sourceMap117_checked : acceptsGraphIso
    (source (graph core117) (root 8) 0 1) SmallGeFourSpectrum169.graph
      sourceMap117=true := by decide +kernel
theorem fusedMap117_checked : acceptsGraphIso
    (fused (graph core117) (root 8) 0 1) SmallGeFourSpectrum107.graph
      fusedMap117=true := by decide +kernel
theorem certified117 : Certified (graph core117) (root 8) 0 1 :=
  of_native_maps core117 SmallGeFourSpectrum169.graph SmallGeFourSpectrum107.graph
    sourceMap117 fusedMap117 sourceMap117_checked fusedMap117_checked
    SmallGeFourComparisons.comparison117
#print axioms sourceMap117_checked
#print axioms fusedMap117_checked
#print axioms certified117
def sourceMap117swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,9,10,11,2,3,6,7,4,5,8] (sourceLabel 8 1 0 v)
def fusedMap117swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,8,9,10,11,4,5,6,7,1,2,3] (fusedLabel 8 1 0 v)
theorem sourceMap117swap_checked : acceptsGraphIso
    (source (graph core117) (root 8) 1 0) SmallGeFourSpectrum169.graph
      sourceMap117swap=true := by decide +kernel
theorem fusedMap117swap_checked : acceptsGraphIso
    (fused (graph core117) (root 8) 1 0) SmallGeFourSpectrum107.graph
      fusedMap117swap=true := by decide +kernel
theorem certified117swap : Certified (graph core117) (root 8) 1 0 :=
  of_native_maps core117 SmallGeFourSpectrum169.graph SmallGeFourSpectrum107.graph
    sourceMap117swap fusedMap117swap sourceMap117swap_checked fusedMap117swap_checked
    SmallGeFourComparisons.comparison117
#print axioms sourceMap117swap_checked
#print axioms fusedMap117swap_checked
#print axioms certified117swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
