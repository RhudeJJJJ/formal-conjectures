/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0207 : Family 5 := level5.get ⟨5,by decide⟩
def sourceMap0207 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 1) → Fin 8 :=
  fun v => ![5,0,1,2,3,4,6,7] (sourceLabel 5 0 0 v)
def fusedMap0207 : (Vertices 5 ⊕ Fin 2) → Fin 8 :=
  fun v => ![5,0,1,2,3,4,6,7] (fusedLabel 5 0 0 v)
theorem sourceMap0207_checked : acceptsGraphIso
    (source (graph core0207) (root 5) 0 0) DegreeOneSmallSpectrum029.graph sourceMap0207=true := by decide +kernel
theorem fusedMap0207_checked : acceptsGraphIso
    (fused (graph core0207) (root 5) 0 0) DegreeOneSmallSpectrum017.graph fusedMap0207=true := by decide +kernel
theorem certified0207 : Certified (graph core0207) (root 5) 0 0 :=
  of_native_maps core0207 DegreeOneSmallSpectrum029.graph DegreeOneSmallSpectrum017.graph
    sourceMap0207 fusedMap0207 sourceMap0207_checked fusedMap0207_checked
    DegreeOneSmallComparisons.comparison0207
#print axioms sourceMap0207_checked
#print axioms fusedMap0207_checked
#print axioms certified0207
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
