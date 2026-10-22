/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0135 : Family 8 := level8.get ⟨211,by decide⟩
def sourceMap0135 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,2,3,4] (sourceLabel 8 0 0 v)
def fusedMap0135 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0135_checked : acceptsGraphIso
    (source (graph core0135) (root 8) 0 0) DegreeOneSmallSpectrum360.graph sourceMap0135=true := by decide +kernel
theorem fusedMap0135_checked : acceptsGraphIso
    (fused (graph core0135) (root 8) 0 0) DegreeOneSmallSpectrum274.graph fusedMap0135=true := by decide +kernel
theorem certified0135 : Certified (graph core0135) (root 8) 0 0 :=
  of_native_maps core0135 DegreeOneSmallSpectrum360.graph DegreeOneSmallSpectrum274.graph
    sourceMap0135 fusedMap0135 sourceMap0135_checked fusedMap0135_checked
    DegreeTwoThreeFiniteComparisons.comparison0135
#print axioms sourceMap0135_checked
#print axioms fusedMap0135_checked
#print axioms certified0135
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
