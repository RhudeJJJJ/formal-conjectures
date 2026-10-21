/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0851 : Family 8 := level8.get ⟨37,by decide⟩
def sourceMap0851 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (sourceLabel 8 0 0 v)
def fusedMap0851 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,6,0,1,2,3,4,5,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0851_checked : acceptsGraphIso
    (source (graph core0851) (root 8) 0 0) DegreeOneSmallSpectrum261.graph sourceMap0851=true := by decide +kernel
theorem fusedMap0851_checked : acceptsGraphIso
    (fused (graph core0851) (root 8) 0 0) DegreeOneSmallSpectrum174.graph fusedMap0851=true := by decide +kernel
theorem certified0851 : Certified (graph core0851) (root 8) 0 0 :=
  of_native_maps core0851 DegreeOneSmallSpectrum261.graph DegreeOneSmallSpectrum174.graph
    sourceMap0851 fusedMap0851 sourceMap0851_checked fusedMap0851_checked
    DegreeOneSmallComparisons.comparison0851
#print axioms sourceMap0851_checked
#print axioms fusedMap0851_checked
#print axioms certified0851
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
