/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0969 : Family 10 := level10.get ⟨1627,by decide⟩
def sourceMap0969 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0969 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0969_checked : acceptsGraphIso
    (source (graph core0969) (root 10) 0 0) DegreeOneSmallSpectrum2006.graph sourceMap0969=true := by decide +kernel
theorem fusedMap0969_checked : acceptsGraphIso
    (fused (graph core0969) (root 10) 0 0) DegreeOneSmallSpectrum1726.graph fusedMap0969=true := by decide +kernel
theorem certified0969 : Certified (graph core0969) (root 10) 0 0 :=
  of_native_maps core0969 DegreeOneSmallSpectrum2006.graph DegreeOneSmallSpectrum1726.graph
    sourceMap0969 fusedMap0969 sourceMap0969_checked fusedMap0969_checked
    DegreeTwoThreeFiniteComparisons.comparison0969
#print axioms sourceMap0969_checked
#print axioms fusedMap0969_checked
#print axioms certified0969
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
