/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0144 : Family 4 := level4.get ⟨4,by decide⟩
def sourceMap0144 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 2) → Fin 8 :=
  fun v => ![0,1,2,3,4,7,5,6] (sourceLabel 4 0 1 v)
def fusedMap0144 : (Vertices 4 ⊕ Fin 3) → Fin 8 :=
  fun v => ![0,1,2,3,4,5,6,7] (fusedLabel 4 0 1 v)
theorem sourceMap0144_checked : acceptsGraphIso
    (source (graph core0144) (root 4) 0 1) DegreeOneSmallSpectrum030.graph sourceMap0144=true := by decide +kernel
theorem fusedMap0144_checked : acceptsGraphIso
    (fused (graph core0144) (root 4) 0 1) DegreeOneSmallSpectrum017.graph fusedMap0144=true := by decide +kernel
theorem certified0144 : Certified (graph core0144) (root 4) 0 1 :=
  of_native_maps core0144 DegreeOneSmallSpectrum030.graph DegreeOneSmallSpectrum017.graph
    sourceMap0144 fusedMap0144 sourceMap0144_checked fusedMap0144_checked
    DegreeOneSmallComparisons.comparison0144
#print axioms sourceMap0144_checked
#print axioms fusedMap0144_checked
#print axioms certified0144
def sourceMap0144swap : (Vertices 4 ⊕ Fin 2 ⊕ Fin 1) → Fin 8 :=
  fun v => ![0,1,2,3,4,5,6,7] (sourceLabel 4 1 0 v)
def fusedMap0144swap : (Vertices 4 ⊕ Fin 3) → Fin 8 :=
  fun v => ![0,1,2,3,4,5,6,7] (fusedLabel 4 1 0 v)
theorem sourceMap0144swap_checked : acceptsGraphIso
    (source (graph core0144) (root 4) 1 0) DegreeOneSmallSpectrum030.graph sourceMap0144swap=true := by decide +kernel
theorem fusedMap0144swap_checked : acceptsGraphIso
    (fused (graph core0144) (root 4) 1 0) DegreeOneSmallSpectrum017.graph fusedMap0144swap=true := by decide +kernel
theorem certified0144swap : Certified (graph core0144) (root 4) 1 0 :=
  of_native_maps core0144 DegreeOneSmallSpectrum030.graph DegreeOneSmallSpectrum017.graph
    sourceMap0144swap fusedMap0144swap sourceMap0144swap_checked fusedMap0144swap_checked
    DegreeOneSmallComparisons.comparison0144
#print axioms sourceMap0144swap_checked
#print axioms fusedMap0144swap_checked
#print axioms certified0144swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
