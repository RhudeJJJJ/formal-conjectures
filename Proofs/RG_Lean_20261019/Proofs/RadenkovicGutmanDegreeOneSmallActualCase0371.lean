/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0371 : Family 6 := level6.get ⟨14,by decide⟩
def sourceMap0371 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,2,3,4,5] (sourceLabel 6 1 1 v)
def fusedMap0371 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 1 1 v)
theorem sourceMap0371_checked : acceptsGraphIso
    (source (graph core0371) (root 6) 1 1) DegreeOneSmallSpectrum329.graph sourceMap0371=true := by decide +kernel
theorem fusedMap0371_checked : acceptsGraphIso
    (fused (graph core0371) (root 6) 1 1) DegreeOneSmallSpectrum222.graph fusedMap0371=true := by decide +kernel
theorem certified0371 : Certified (graph core0371) (root 6) 1 1 :=
  of_native_maps core0371 DegreeOneSmallSpectrum329.graph DegreeOneSmallSpectrum222.graph
    sourceMap0371 fusedMap0371 sourceMap0371_checked fusedMap0371_checked
    DegreeOneSmallComparisons.comparison0371
#print axioms sourceMap0371_checked
#print axioms fusedMap0371_checked
#print axioms certified0371
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
