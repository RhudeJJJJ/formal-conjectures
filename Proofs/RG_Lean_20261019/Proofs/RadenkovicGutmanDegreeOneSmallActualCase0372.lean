/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0372 : Family 6 := level6.get ⟨14,by decide⟩
def sourceMap0372 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,6,7,8,9,10,11,4,5,1,2,3] (sourceLabel 6 1 2 v)
def fusedMap0372 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 1 2 v)
theorem sourceMap0372_checked : acceptsGraphIso
    (source (graph core0372) (root 6) 1 2) DegreeOneSmallSpectrum572.graph sourceMap0372=true := by decide +kernel
theorem fusedMap0372_checked : acceptsGraphIso
    (fused (graph core0372) (root 6) 1 2) DegreeOneSmallSpectrum387.graph fusedMap0372=true := by decide +kernel
theorem certified0372 : Certified (graph core0372) (root 6) 1 2 :=
  of_native_maps core0372 DegreeOneSmallSpectrum572.graph DegreeOneSmallSpectrum387.graph
    sourceMap0372 fusedMap0372 sourceMap0372_checked fusedMap0372_checked
    DegreeOneSmallComparisons.comparison0372
#print axioms sourceMap0372_checked
#print axioms fusedMap0372_checked
#print axioms certified0372
def sourceMap0372swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,6,7,8,9,10,11,1,2,3,4,5] (sourceLabel 6 2 1 v)
def fusedMap0372swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 2 1 v)
theorem sourceMap0372swap_checked : acceptsGraphIso
    (source (graph core0372) (root 6) 2 1) DegreeOneSmallSpectrum572.graph sourceMap0372swap=true := by decide +kernel
theorem fusedMap0372swap_checked : acceptsGraphIso
    (fused (graph core0372) (root 6) 2 1) DegreeOneSmallSpectrum387.graph fusedMap0372swap=true := by decide +kernel
theorem certified0372swap : Certified (graph core0372) (root 6) 2 1 :=
  of_native_maps core0372 DegreeOneSmallSpectrum572.graph DegreeOneSmallSpectrum387.graph
    sourceMap0372swap fusedMap0372swap sourceMap0372swap_checked fusedMap0372swap_checked
    DegreeOneSmallComparisons.comparison0372
#print axioms sourceMap0372swap_checked
#print axioms fusedMap0372swap_checked
#print axioms certified0372swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
