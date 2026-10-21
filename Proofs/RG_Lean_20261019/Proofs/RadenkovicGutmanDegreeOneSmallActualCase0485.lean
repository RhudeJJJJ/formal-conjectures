/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0485 : Family 7 := level7.get ⟨7,by decide⟩
def sourceMap0485 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 3) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 7 0 2 v)
def fusedMap0485 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 0 2 v)
theorem sourceMap0485_checked : acceptsGraphIso
    (source (graph core0485) (root 7) 0 2) DegreeOneSmallSpectrum426.graph sourceMap0485=true := by decide +kernel
theorem fusedMap0485_checked : acceptsGraphIso
    (fused (graph core0485) (root 7) 0 2) DegreeOneSmallSpectrum370.graph fusedMap0485=true := by decide +kernel
theorem certified0485 : Certified (graph core0485) (root 7) 0 2 :=
  of_native_maps core0485 DegreeOneSmallSpectrum426.graph DegreeOneSmallSpectrum370.graph
    sourceMap0485 fusedMap0485 sourceMap0485_checked fusedMap0485_checked
    DegreeOneSmallComparisons.comparison0485
#print axioms sourceMap0485_checked
#print axioms fusedMap0485_checked
#print axioms certified0485
def sourceMap0485swap : (Vertices 7 ⊕ Fin 3 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 7 2 0 v)
def fusedMap0485swap : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 2 0 v)
theorem sourceMap0485swap_checked : acceptsGraphIso
    (source (graph core0485) (root 7) 2 0) DegreeOneSmallSpectrum426.graph sourceMap0485swap=true := by decide +kernel
theorem fusedMap0485swap_checked : acceptsGraphIso
    (fused (graph core0485) (root 7) 2 0) DegreeOneSmallSpectrum370.graph fusedMap0485swap=true := by decide +kernel
theorem certified0485swap : Certified (graph core0485) (root 7) 2 0 :=
  of_native_maps core0485 DegreeOneSmallSpectrum426.graph DegreeOneSmallSpectrum370.graph
    sourceMap0485swap fusedMap0485swap sourceMap0485swap_checked fusedMap0485swap_checked
    DegreeOneSmallComparisons.comparison0485
#print axioms sourceMap0485swap_checked
#print axioms fusedMap0485swap_checked
#print axioms certified0485swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
