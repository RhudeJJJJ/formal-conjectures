/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0066 : Family 8 := level8.get ⟨19,by decide⟩
def sourceMap0066 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,3,4,5] (sourceLabel 8 0 0 v)
def fusedMap0066 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![2,1,0,6,7,8,9,10,5,3,4] (fusedLabel 8 0 0 v)
theorem sourceMap0066_checked : acceptsGraphIso
    (source (graph core0066) (root 8) 0 0) DegreeOneSmallSpectrum173.graph sourceMap0066=true := by decide +kernel
theorem fusedMap0066_checked : acceptsGraphIso
    (fused (graph core0066) (root 8) 0 0) DegreeOneSmallSpectrum213.graph fusedMap0066=true := by decide +kernel
theorem certified0066 : Certified (graph core0066) (root 8) 0 0 :=
  of_native_maps core0066 DegreeOneSmallSpectrum173.graph DegreeOneSmallSpectrum213.graph
    sourceMap0066 fusedMap0066 sourceMap0066_checked fusedMap0066_checked
    DegreeTwoThreeFiniteComparisons.comparison0066
#print axioms sourceMap0066_checked
#print axioms fusedMap0066_checked
#print axioms certified0066
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
