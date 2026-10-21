/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0629 : Family 7 := level7.get ⟨43,by decide⟩
def sourceMap0629 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0629 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0629_checked : acceptsGraphIso
    (source (graph core0629) (root 7) 0 2) DegreeOneSmallSpectrum527.graph sourceMap0629=true := by decide +kernel
theorem fusedMap0629_checked : acceptsGraphIso
    (fused (graph core0629) (root 7) 0 2) DegreeOneSmallSpectrum528.graph fusedMap0629=true := by decide +kernel
theorem certified0629 : Certified (graph core0629) (root 7) 0 2 :=
  of_native_maps core0629 DegreeOneSmallSpectrum527.graph DegreeOneSmallSpectrum528.graph
    sourceMap0629 fusedMap0629 sourceMap0629_checked fusedMap0629_checked
    DegreeOneSmallComparisons.comparison0629
#print axioms sourceMap0629_checked
#print axioms fusedMap0629_checked
#print axioms certified0629
def sourceMap0629swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0629swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0629swap_checked : acceptsGraphIso
    (source (graph core0629) (root 7) 2 0) DegreeOneSmallSpectrum527.graph sourceMap0629swap=true := by decide +kernel
theorem fusedMap0629swap_checked : acceptsGraphIso
    (fused (graph core0629) (root 7) 2 0) DegreeOneSmallSpectrum528.graph fusedMap0629swap=true := by decide +kernel
theorem certified0629swap : Certified (graph core0629) (root 7) 2 0 :=
  of_native_maps core0629 DegreeOneSmallSpectrum527.graph DegreeOneSmallSpectrum528.graph
    sourceMap0629swap fusedMap0629swap sourceMap0629swap_checked fusedMap0629swap_checked
    DegreeOneSmallComparisons.comparison0629
#print axioms sourceMap0629swap_checked
#print axioms fusedMap0629swap_checked
#print axioms certified0629swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
