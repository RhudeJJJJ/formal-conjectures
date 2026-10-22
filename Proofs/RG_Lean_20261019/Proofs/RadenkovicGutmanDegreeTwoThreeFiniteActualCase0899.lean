/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0899 : Family 10 := level10.get ⟨1445,by decide⟩
def sourceMap0899 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0899 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0899_checked : acceptsGraphIso
    (source (graph core0899) (root 10) 0 0) DegreeOneSmallSpectrum1483.graph sourceMap0899=true := by decide +kernel
theorem fusedMap0899_checked : acceptsGraphIso
    (fused (graph core0899) (root 10) 0 0) DegreeOneSmallSpectrum1482.graph fusedMap0899=true := by decide +kernel
theorem certified0899 : Certified (graph core0899) (root 10) 0 0 :=
  of_native_maps core0899 DegreeOneSmallSpectrum1483.graph DegreeOneSmallSpectrum1482.graph
    sourceMap0899 fusedMap0899 sourceMap0899_checked fusedMap0899_checked
    DegreeTwoThreeFiniteComparisons.comparison0899
#print axioms sourceMap0899_checked
#print axioms fusedMap0899_checked
#print axioms certified0899
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
