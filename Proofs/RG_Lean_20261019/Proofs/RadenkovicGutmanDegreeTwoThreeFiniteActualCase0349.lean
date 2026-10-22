/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0349 : Family 9 := level9.get ⟨555,by decide⟩
def sourceMap0349 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0349 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0349_checked : acceptsGraphIso
    (source (graph core0349) (root 9) 0 0) DegreeTwoThreeSpectrum523.graph sourceMap0349=true := by decide +kernel
theorem fusedMap0349_checked : acceptsGraphIso
    (fused (graph core0349) (root 9) 0 0) DegreeOneSmallSpectrum615.graph fusedMap0349=true := by decide +kernel
theorem certified0349 : Certified (graph core0349) (root 9) 0 0 :=
  of_native_maps core0349 DegreeTwoThreeSpectrum523.graph DegreeOneSmallSpectrum615.graph
    sourceMap0349 fusedMap0349 sourceMap0349_checked fusedMap0349_checked
    DegreeTwoThreeFiniteComparisons.comparison0349
#print axioms sourceMap0349_checked
#print axioms fusedMap0349_checked
#print axioms certified0349
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
