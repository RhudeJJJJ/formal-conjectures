/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0854 : Family 8 := level8.get ⟨37,by decide⟩
def sourceMap0854 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,12,8,9,10,11] (sourceLabel 8 1 1 v)
def fusedMap0854 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0854_checked : acceptsGraphIso
    (source (graph core0854) (root 8) 1 1) DegreeOneSmallSpectrum1068.graph sourceMap0854=true := by decide +kernel
theorem fusedMap0854_checked : acceptsGraphIso
    (fused (graph core0854) (root 8) 1 1) DegreeOneSmallSpectrum865.graph fusedMap0854=true := by decide +kernel
theorem certified0854 : Certified (graph core0854) (root 8) 1 1 :=
  of_native_maps core0854 DegreeOneSmallSpectrum1068.graph DegreeOneSmallSpectrum865.graph
    sourceMap0854 fusedMap0854 sourceMap0854_checked fusedMap0854_checked
    DegreeOneSmallComparisons.comparison0854
#print axioms sourceMap0854_checked
#print axioms fusedMap0854_checked
#print axioms certified0854
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
