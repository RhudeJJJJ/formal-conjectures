/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0252 : Family 5 := level5.get ⟨9,by decide⟩
def sourceMap0252 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12] (sourceLabel 5 1 4 v)
def fusedMap0252 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 1 4 v)
theorem sourceMap0252_checked : acceptsGraphIso
    (source (graph core0252) (root 5) 1 4) DegreeOneSmallSpectrum1370.graph sourceMap0252=true := by decide +kernel
theorem fusedMap0252_checked : acceptsGraphIso
    (fused (graph core0252) (root 5) 1 4) DegreeOneSmallSpectrum922.graph fusedMap0252=true := by decide +kernel
theorem certified0252 : Certified (graph core0252) (root 5) 1 4 :=
  of_native_maps core0252 DegreeOneSmallSpectrum1370.graph DegreeOneSmallSpectrum922.graph
    sourceMap0252 fusedMap0252 sourceMap0252_checked fusedMap0252_checked
    DegreeOneSmallComparisons.comparison0252
#print axioms sourceMap0252_checked
#print axioms fusedMap0252_checked
#print axioms certified0252
def sourceMap0252swap : (Vertices 5 ⊕ Fin 5 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,0,9,10,11,12,7,8] (sourceLabel 5 4 1 v)
def fusedMap0252swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 4 1 v)
theorem sourceMap0252swap_checked : acceptsGraphIso
    (source (graph core0252) (root 5) 4 1) DegreeOneSmallSpectrum1370.graph sourceMap0252swap=true := by decide +kernel
theorem fusedMap0252swap_checked : acceptsGraphIso
    (fused (graph core0252) (root 5) 4 1) DegreeOneSmallSpectrum922.graph fusedMap0252swap=true := by decide +kernel
theorem certified0252swap : Certified (graph core0252) (root 5) 4 1 :=
  of_native_maps core0252 DegreeOneSmallSpectrum1370.graph DegreeOneSmallSpectrum922.graph
    sourceMap0252swap fusedMap0252swap sourceMap0252swap_checked fusedMap0252swap_checked
    DegreeOneSmallComparisons.comparison0252
#print axioms sourceMap0252swap_checked
#print axioms fusedMap0252swap_checked
#print axioms certified0252swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
