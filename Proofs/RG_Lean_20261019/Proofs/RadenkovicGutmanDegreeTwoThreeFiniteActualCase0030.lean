/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0030 : Family 7 := level7.get ⟨20,by decide⟩
def sourceMap0030 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![2,1,0,6,7,8,9,3,4,5] (sourceLabel 7 0 0 v)
def fusedMap0030 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,5,6,7,8,9,4,2,3] (fusedLabel 7 0 0 v)
theorem sourceMap0030_checked : acceptsGraphIso
    (source (graph core0030) (root 7) 0 0) DegreeOneSmallSpectrum106.graph sourceMap0030=true := by decide +kernel
theorem fusedMap0030_checked : acceptsGraphIso
    (fused (graph core0030) (root 7) 0 0) DegreeOneSmallSpectrum085.graph fusedMap0030=true := by decide +kernel
theorem certified0030 : Certified (graph core0030) (root 7) 0 0 :=
  of_native_maps core0030 DegreeOneSmallSpectrum106.graph DegreeOneSmallSpectrum085.graph
    sourceMap0030 fusedMap0030 sourceMap0030_checked fusedMap0030_checked
    DegreeTwoThreeFiniteComparisons.comparison0030
#print axioms sourceMap0030_checked
#print axioms fusedMap0030_checked
#print axioms certified0030
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
