/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons06
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core113 : Family 8 := level8.get ⟨160,by decide⟩
def sourceMap113 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,4,5,6,7,2,3] (sourceLabel 8 0 1 v)
def fusedMap113 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,9,10,11,6,7,8] (fusedLabel 8 0 1 v)
theorem sourceMap113_checked : acceptsGraphIso
    (source (graph core113) (root 8) 0 1) SmallGeFourSpectrum182.graph
      sourceMap113=true := by decide +kernel
theorem fusedMap113_checked : acceptsGraphIso
    (fused (graph core113) (root 8) 0 1) SmallGeFourSpectrum106.graph
      fusedMap113=true := by decide +kernel
theorem certified113 : Certified (graph core113) (root 8) 0 1 :=
  of_native_maps core113 SmallGeFourSpectrum182.graph SmallGeFourSpectrum106.graph
    sourceMap113 fusedMap113 sourceMap113_checked fusedMap113_checked
    SmallGeFourComparisons.comparison113
#print axioms sourceMap113_checked
#print axioms fusedMap113_checked
#print axioms certified113
def sourceMap113swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,4,5,6,2,3,7] (sourceLabel 8 1 0 v)
def fusedMap113swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,9,10,11,6,7,8] (fusedLabel 8 1 0 v)
theorem sourceMap113swap_checked : acceptsGraphIso
    (source (graph core113) (root 8) 1 0) SmallGeFourSpectrum182.graph
      sourceMap113swap=true := by decide +kernel
theorem fusedMap113swap_checked : acceptsGraphIso
    (fused (graph core113) (root 8) 1 0) SmallGeFourSpectrum106.graph
      fusedMap113swap=true := by decide +kernel
theorem certified113swap : Certified (graph core113) (root 8) 1 0 :=
  of_native_maps core113 SmallGeFourSpectrum182.graph SmallGeFourSpectrum106.graph
    sourceMap113swap fusedMap113swap sourceMap113swap_checked fusedMap113swap_checked
    SmallGeFourComparisons.comparison113
#print axioms sourceMap113swap_checked
#print axioms fusedMap113swap_checked
#print axioms certified113swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
