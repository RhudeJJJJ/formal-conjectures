/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanSmallGeFourComparisons00
namespace Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core011 : Family 4 := level4.get ⟨8,by decide⟩
def sourceMap011 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,4,5,6,7,1,2,3,8,9,10,11] (sourceLabel 4 2 3 v)
def fusedMap011 : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11] (fusedLabel 4 2 3 v)
theorem sourceMap011_checked : acceptsGraphIso
    (source (graph core011) (root 4) 2 3) SmallGeFourSpectrum108.graph
      sourceMap011=true := by decide +kernel
theorem fusedMap011_checked : acceptsGraphIso
    (fused (graph core011) (root 4) 2 3) SmallGeFourSpectrum094.graph
      fusedMap011=true := by decide +kernel
theorem certified011 : Certified (graph core011) (root 4) 2 3 :=
  of_native_maps core011 SmallGeFourSpectrum108.graph SmallGeFourSpectrum094.graph
    sourceMap011 fusedMap011 sourceMap011_checked fusedMap011_checked
    SmallGeFourComparisons.comparison011
#print axioms sourceMap011_checked
#print axioms fusedMap011_checked
#print axioms certified011
def sourceMap011swap : (Vertices 4 ⊕ Fin 4 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,4,5,6,7,8,9,10,11,1,2,3] (sourceLabel 4 3 2 v)
def fusedMap011swap : (Vertices 4 ⊕ Fin 7) → Fin 12 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11] (fusedLabel 4 3 2 v)
theorem sourceMap011swap_checked : acceptsGraphIso
    (source (graph core011) (root 4) 3 2) SmallGeFourSpectrum108.graph
      sourceMap011swap=true := by decide +kernel
theorem fusedMap011swap_checked : acceptsGraphIso
    (fused (graph core011) (root 4) 3 2) SmallGeFourSpectrum094.graph
      fusedMap011swap=true := by decide +kernel
theorem certified011swap : Certified (graph core011) (root 4) 3 2 :=
  of_native_maps core011 SmallGeFourSpectrum108.graph SmallGeFourSpectrum094.graph
    sourceMap011swap fusedMap011swap sourceMap011swap_checked fusedMap011swap_checked
    SmallGeFourComparisons.comparison011
#print axioms sourceMap011swap_checked
#print axioms fusedMap011swap_checked
#print axioms certified011swap
end Gebendorfer.RadenkovicGutman.SmallGeFourActualCases
