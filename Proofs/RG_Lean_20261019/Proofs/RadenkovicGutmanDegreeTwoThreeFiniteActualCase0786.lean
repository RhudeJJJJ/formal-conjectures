/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0786 : Family 10 := level10.get ⟨1180,by decide⟩
def sourceMap0786 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0786 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,9,10,11,12,8,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0786_checked : acceptsGraphIso
    (source (graph core0786) (root 10) 0 0) DegreeOneSmallSpectrum1871.graph sourceMap0786=true := by decide +kernel
theorem fusedMap0786_checked : acceptsGraphIso
    (fused (graph core0786) (root 10) 0 0) DegreeOneSmallSpectrum1869.graph fusedMap0786=true := by decide +kernel
theorem certified0786 : Certified (graph core0786) (root 10) 0 0 :=
  of_native_maps core0786 DegreeOneSmallSpectrum1871.graph DegreeOneSmallSpectrum1869.graph
    sourceMap0786 fusedMap0786 sourceMap0786_checked fusedMap0786_checked
    DegreeTwoThreeFiniteComparisons.comparison0786
#print axioms sourceMap0786_checked
#print axioms fusedMap0786_checked
#print axioms certified0786
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
