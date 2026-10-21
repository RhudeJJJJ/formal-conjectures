/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons01
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core023 : Family 5 := level5.get ⟨19,by decide⟩
def sourceMap023 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 3) → Fin 10 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9] (sourceLabel 5 0 2 v)
def fusedMap023 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9] (fusedLabel 5 0 2 v)
theorem sourceMap023_checked : acceptsGraphIso
    (source (graph core023) (root 5) 0 2) SmallGeFourSpectrum026.graph
      sourceMap023=true := by decide +kernel
theorem fusedMap023_checked : acceptsGraphIso
    (fused (graph core023) (root 5) 0 2) SmallGeFourSpectrum015.graph
      fusedMap023=true := by decide +kernel
theorem certified023 : Certified (graph core023) (root 5) 0 2 :=
  of_native_maps core023 SmallGeFourSpectrum026.graph SmallGeFourSpectrum015.graph
    sourceMap023 fusedMap023 sourceMap023_checked fusedMap023_checked
    SmallGeFourComparisons.comparison023
#print axioms sourceMap023_checked
#print axioms fusedMap023_checked
#print axioms certified023
def sourceMap023swap : (Vertices 5 ⊕ Fin 3 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,2,3,4,5,6,0,8,9,7] (sourceLabel 5 2 0 v)
def fusedMap023swap : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9] (fusedLabel 5 2 0 v)
theorem sourceMap023swap_checked : acceptsGraphIso
    (source (graph core023) (root 5) 2 0) SmallGeFourSpectrum026.graph
      sourceMap023swap=true := by decide +kernel
theorem fusedMap023swap_checked : acceptsGraphIso
    (fused (graph core023) (root 5) 2 0) SmallGeFourSpectrum015.graph
      fusedMap023swap=true := by decide +kernel
theorem certified023swap : Certified (graph core023) (root 5) 2 0 :=
  of_native_maps core023 SmallGeFourSpectrum026.graph SmallGeFourSpectrum015.graph
    sourceMap023swap fusedMap023swap sourceMap023swap_checked fusedMap023swap_checked
    SmallGeFourComparisons.comparison023
#print axioms sourceMap023swap_checked
#print axioms fusedMap023swap_checked
#print axioms certified023swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
