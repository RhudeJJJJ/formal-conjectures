/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0054 : Family 7 := level7.get ⟨83,by decide⟩
def sourceMap0054 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,5,6,7,8,9,2,3,4] (sourceLabel 7 0 0 v)
def fusedMap0054 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,9,7,8] (fusedLabel 7 0 0 v)
theorem sourceMap0054_checked : acceptsGraphIso
    (source (graph core0054) (root 7) 0 0) DegreeTwoThreeSpectrum148.graph sourceMap0054=true := by decide +kernel
theorem fusedMap0054_checked : acceptsGraphIso
    (fused (graph core0054) (root 7) 0 0) DegreeOneSmallSpectrum132.graph fusedMap0054=true := by decide +kernel
theorem certified0054 : Certified (graph core0054) (root 7) 0 0 :=
  of_native_maps core0054 DegreeTwoThreeSpectrum148.graph DegreeOneSmallSpectrum132.graph
    sourceMap0054 fusedMap0054 sourceMap0054_checked fusedMap0054_checked
    DegreeTwoThreeFiniteComparisons.comparison0054
#print axioms sourceMap0054_checked
#print axioms fusedMap0054_checked
#print axioms certified0054
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
