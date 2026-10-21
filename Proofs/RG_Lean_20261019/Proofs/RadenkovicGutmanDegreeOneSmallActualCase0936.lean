/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0936 : Family 8 := level8.get ⟨70,by decide⟩
def sourceMap0936 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,4,2,3] (sourceLabel 8 0 1 v)
def fusedMap0936 : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 0 1 v)
theorem sourceMap0936_checked : acceptsGraphIso
    (source (graph core0936) (root 8) 0 1) DegreeOneSmallSpectrum552.graph sourceMap0936=true := by decide +kernel
theorem fusedMap0936_checked : acceptsGraphIso
    (fused (graph core0936) (root 8) 0 1) DegreeOneSmallSpectrum563.graph fusedMap0936=true := by decide +kernel
theorem certified0936 : Certified (graph core0936) (root 8) 0 1 :=
  of_native_maps core0936 DegreeOneSmallSpectrum552.graph DegreeOneSmallSpectrum563.graph
    sourceMap0936 fusedMap0936 sourceMap0936_checked fusedMap0936_checked
    DegreeOneSmallComparisons.comparison0936
#print axioms sourceMap0936_checked
#print axioms fusedMap0936_checked
#print axioms certified0936
def sourceMap0936swap : (Vertices 8 ⊕ Fin 2 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (sourceLabel 8 1 0 v)
def fusedMap0936swap : (Vertices 8 ⊕ Fin 3) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (fusedLabel 8 1 0 v)
theorem sourceMap0936swap_checked : acceptsGraphIso
    (source (graph core0936) (root 8) 1 0) DegreeOneSmallSpectrum552.graph sourceMap0936swap=true := by decide +kernel
theorem fusedMap0936swap_checked : acceptsGraphIso
    (fused (graph core0936) (root 8) 1 0) DegreeOneSmallSpectrum563.graph fusedMap0936swap=true := by decide +kernel
theorem certified0936swap : Certified (graph core0936) (root 8) 1 0 :=
  of_native_maps core0936 DegreeOneSmallSpectrum552.graph DegreeOneSmallSpectrum563.graph
    sourceMap0936swap fusedMap0936swap sourceMap0936swap_checked fusedMap0936swap_checked
    DegreeOneSmallComparisons.comparison0936
#print axioms sourceMap0936swap_checked
#print axioms fusedMap0936swap_checked
#print axioms certified0936swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
