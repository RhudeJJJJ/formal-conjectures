/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0233 : Family 5 := level5.get ⟨8,by decide⟩
def sourceMap0233 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,9,6,7,8] (sourceLabel 5 0 2 v)
def fusedMap0233 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 0 2 v)
theorem sourceMap0233_checked : acceptsGraphIso
    (source (graph core0233) (root 5) 0 2) DegreeOneSmallSpectrum137.graph sourceMap0233=true := by decide +kernel
theorem fusedMap0233_checked : acceptsGraphIso
    (fused (graph core0233) (root 5) 0 2) DegreeOneSmallSpectrum081.graph fusedMap0233=true := by decide +kernel
theorem certified0233 : Certified (graph core0233) (root 5) 0 2 :=
  of_native_maps core0233 DegreeOneSmallSpectrum137.graph DegreeOneSmallSpectrum081.graph
    sourceMap0233 fusedMap0233 sourceMap0233_checked fusedMap0233_checked
    DegreeOneSmallComparisons.comparison0233
#print axioms sourceMap0233_checked
#print axioms fusedMap0233_checked
#print axioms certified0233
def sourceMap0233swap : (Vertices 5 ⊕ Fin 3 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 5 2 0 v)
def fusedMap0233swap : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 2 0 v)
theorem sourceMap0233swap_checked : acceptsGraphIso
    (source (graph core0233) (root 5) 2 0) DegreeOneSmallSpectrum137.graph sourceMap0233swap=true := by decide +kernel
theorem fusedMap0233swap_checked : acceptsGraphIso
    (fused (graph core0233) (root 5) 2 0) DegreeOneSmallSpectrum081.graph fusedMap0233swap=true := by decide +kernel
theorem certified0233swap : Certified (graph core0233) (root 5) 2 0 :=
  of_native_maps core0233 DegreeOneSmallSpectrum137.graph DegreeOneSmallSpectrum081.graph
    sourceMap0233swap fusedMap0233swap sourceMap0233swap_checked fusedMap0233swap_checked
    DegreeOneSmallComparisons.comparison0233
#print axioms sourceMap0233swap_checked
#print axioms fusedMap0233swap_checked
#print axioms certified0233swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
