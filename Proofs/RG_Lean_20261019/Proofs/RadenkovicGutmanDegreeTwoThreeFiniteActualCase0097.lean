/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0097 : Family 8 := level8.get ⟨118,by decide⟩
def sourceMap0097 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap0097 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0097_checked : acceptsGraphIso
    (source (graph core0097) (root 8) 0 0) DegreeOneSmallSpectrum297.graph sourceMap0097=true := by decide +kernel
theorem fusedMap0097_checked : acceptsGraphIso
    (fused (graph core0097) (root 8) 0 0) DegreeOneSmallSpectrum295.graph fusedMap0097=true := by decide +kernel
theorem certified0097 : Certified (graph core0097) (root 8) 0 0 :=
  of_native_maps core0097 DegreeOneSmallSpectrum297.graph DegreeOneSmallSpectrum295.graph
    sourceMap0097 fusedMap0097 sourceMap0097_checked fusedMap0097_checked
    DegreeTwoThreeFiniteComparisons.comparison0097
#print axioms sourceMap0097_checked
#print axioms fusedMap0097_checked
#print axioms certified0097
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
