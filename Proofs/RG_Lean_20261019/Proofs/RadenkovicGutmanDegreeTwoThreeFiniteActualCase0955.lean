/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0955 : Family 10 := level10.get ⟨1588,by decide⟩
def sourceMap0955 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0955 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0955_checked : acceptsGraphIso
    (source (graph core0955) (root 10) 0 0) DegreeOneSmallSpectrum1648.graph sourceMap0955=true := by decide +kernel
theorem fusedMap0955_checked : acceptsGraphIso
    (fused (graph core0955) (root 10) 0 0) DegreeOneSmallSpectrum1647.graph fusedMap0955=true := by decide +kernel
theorem certified0955 : Certified (graph core0955) (root 10) 0 0 :=
  of_native_maps core0955 DegreeOneSmallSpectrum1648.graph DegreeOneSmallSpectrum1647.graph
    sourceMap0955 fusedMap0955 sourceMap0955_checked fusedMap0955_checked
    DegreeTwoThreeFiniteComparisons.comparison0955
#print axioms sourceMap0955_checked
#print axioms fusedMap0955_checked
#print axioms certified0955
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
