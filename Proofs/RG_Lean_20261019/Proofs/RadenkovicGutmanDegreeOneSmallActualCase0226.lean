/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0226 : Family 5 := level5.get ⟨6,by decide⟩
def sourceMap0226 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,9,10,6,7,8] (sourceLabel 5 1 2 v)
def fusedMap0226 : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (fusedLabel 5 1 2 v)
theorem sourceMap0226_checked : acceptsGraphIso
    (source (graph core0226) (root 5) 1 2) DegreeOneSmallSpectrum299.graph sourceMap0226=true := by decide +kernel
theorem fusedMap0226_checked : acceptsGraphIso
    (fused (graph core0226) (root 5) 1 2) DegreeOneSmallSpectrum182.graph fusedMap0226=true := by decide +kernel
theorem certified0226 : Certified (graph core0226) (root 5) 1 2 :=
  of_native_maps core0226 DegreeOneSmallSpectrum299.graph DegreeOneSmallSpectrum182.graph
    sourceMap0226 fusedMap0226 sourceMap0226_checked fusedMap0226_checked
    DegreeOneSmallComparisons.comparison0226
#print axioms sourceMap0226_checked
#print axioms fusedMap0226_checked
#print axioms certified0226
def sourceMap0226swap : (Vertices 5 ⊕ Fin 3 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 5 2 1 v)
def fusedMap0226swap : (Vertices 5 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (fusedLabel 5 2 1 v)
theorem sourceMap0226swap_checked : acceptsGraphIso
    (source (graph core0226) (root 5) 2 1) DegreeOneSmallSpectrum299.graph sourceMap0226swap=true := by decide +kernel
theorem fusedMap0226swap_checked : acceptsGraphIso
    (fused (graph core0226) (root 5) 2 1) DegreeOneSmallSpectrum182.graph fusedMap0226swap=true := by decide +kernel
theorem certified0226swap : Certified (graph core0226) (root 5) 2 1 :=
  of_native_maps core0226 DegreeOneSmallSpectrum299.graph DegreeOneSmallSpectrum182.graph
    sourceMap0226swap fusedMap0226swap sourceMap0226swap_checked fusedMap0226swap_checked
    DegreeOneSmallComparisons.comparison0226
#print axioms sourceMap0226swap_checked
#print axioms fusedMap0226swap_checked
#print axioms certified0226swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
