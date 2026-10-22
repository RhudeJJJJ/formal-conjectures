/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0464 : Family 10 := level10.get ⟨277,by decide⟩
def sourceMap0464 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0464 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,10,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap0464_checked : acceptsGraphIso
    (source (graph core0464) (root 10) 0 0) DegreeOneSmallSpectrum1018.graph sourceMap0464=true := by decide +kernel
theorem fusedMap0464_checked : acceptsGraphIso
    (fused (graph core0464) (root 10) 0 0) DegreeOneSmallSpectrum1270.graph fusedMap0464=true := by decide +kernel
theorem certified0464 : Certified (graph core0464) (root 10) 0 0 :=
  of_native_maps core0464 DegreeOneSmallSpectrum1018.graph DegreeOneSmallSpectrum1270.graph
    sourceMap0464 fusedMap0464 sourceMap0464_checked fusedMap0464_checked
    DegreeTwoThreeFiniteComparisons.comparison0464
#print axioms sourceMap0464_checked
#print axioms fusedMap0464_checked
#print axioms certified0464
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
