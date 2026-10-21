/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons01
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core027 : Family 5 := level5.get ⟨19,by decide⟩
def sourceMap027 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,3,4,5,6,7,1,2,8,9,10] (sourceLabel 5 1 2 v)
def fusedMap027 : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10] (fusedLabel 5 1 2 v)
theorem sourceMap027_checked : acceptsGraphIso
    (source (graph core027) (root 5) 1 2) SmallGeFourSpectrum060.graph
      sourceMap027=true := by decide +kernel
theorem fusedMap027_checked : acceptsGraphIso
    (fused (graph core027) (root 5) 1 2) SmallGeFourSpectrum044.graph
      fusedMap027=true := by decide +kernel
theorem certified027 : Certified (graph core027) (root 5) 1 2 :=
  of_native_maps core027 SmallGeFourSpectrum060.graph SmallGeFourSpectrum044.graph
    sourceMap027 fusedMap027 sourceMap027_checked fusedMap027_checked
    SmallGeFourComparisons.comparison027
#print axioms sourceMap027_checked
#print axioms fusedMap027_checked
#print axioms certified027
def sourceMap027swap : (Vertices 5 ⊕ Fin 3 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,3,4,5,6,7,8,9,10,1,2] (sourceLabel 5 2 1 v)
def fusedMap027swap : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10] (fusedLabel 5 2 1 v)
theorem sourceMap027swap_checked : acceptsGraphIso
    (source (graph core027) (root 5) 2 1) SmallGeFourSpectrum060.graph
      sourceMap027swap=true := by decide +kernel
theorem fusedMap027swap_checked : acceptsGraphIso
    (fused (graph core027) (root 5) 2 1) SmallGeFourSpectrum044.graph
      fusedMap027swap=true := by decide +kernel
theorem certified027swap : Certified (graph core027) (root 5) 2 1 :=
  of_native_maps core027 SmallGeFourSpectrum060.graph SmallGeFourSpectrum044.graph
    sourceMap027swap fusedMap027swap sourceMap027swap_checked fusedMap027swap_checked
    SmallGeFourComparisons.comparison027
#print axioms sourceMap027swap_checked
#print axioms fusedMap027swap_checked
#print axioms certified027swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
