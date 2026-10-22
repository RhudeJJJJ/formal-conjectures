/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0889 : Family 10 := level10.get ⟨1423,by decide⟩
def sourceMap0889 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0889 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0889_checked : acceptsGraphIso
    (source (graph core0889) (root 10) 0 0) DegreeOneSmallSpectrum1951.graph sourceMap0889=true := by decide +kernel
theorem fusedMap0889_checked : acceptsGraphIso
    (fused (graph core0889) (root 10) 0 0) DegreeOneSmallSpectrum1927.graph fusedMap0889=true := by decide +kernel
theorem certified0889 : Certified (graph core0889) (root 10) 0 0 :=
  of_native_maps core0889 DegreeOneSmallSpectrum1951.graph DegreeOneSmallSpectrum1927.graph
    sourceMap0889 fusedMap0889 sourceMap0889_checked fusedMap0889_checked
    DegreeTwoThreeFiniteComparisons.comparison0889
#print axioms sourceMap0889_checked
#print axioms fusedMap0889_checked
#print axioms certified0889
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
