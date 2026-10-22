/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0793 : Family 10 := level10.get ⟨1197,by decide⟩
def sourceMap0793 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,5,6,7,8,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0793 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,9,10,11,12,8,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0793_checked : acceptsGraphIso
    (source (graph core0793) (root 10) 0 0) DegreeOneSmallSpectrum1622.graph sourceMap0793=true := by decide +kernel
theorem fusedMap0793_checked : acceptsGraphIso
    (fused (graph core0793) (root 10) 0 0) DegreeOneSmallSpectrum1874.graph fusedMap0793=true := by decide +kernel
theorem certified0793 : Certified (graph core0793) (root 10) 0 0 :=
  of_native_maps core0793 DegreeOneSmallSpectrum1622.graph DegreeOneSmallSpectrum1874.graph
    sourceMap0793 fusedMap0793 sourceMap0793_checked fusedMap0793_checked
    DegreeTwoThreeFiniteComparisons.comparison0793
#print axioms sourceMap0793_checked
#print axioms fusedMap0793_checked
#print axioms certified0793
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
