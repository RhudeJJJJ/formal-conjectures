/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0522 : Family 10 := level10.get ⟨463,by decide⟩
def sourceMap0522 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0522 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0522_checked : acceptsGraphIso
    (source (graph core0522) (root 10) 0 0) DegreeOneSmallSpectrum955.graph sourceMap0522=true := by decide +kernel
theorem fusedMap0522_checked : acceptsGraphIso
    (fused (graph core0522) (root 10) 0 0) DegreeOneSmallSpectrum950.graph fusedMap0522=true := by decide +kernel
theorem certified0522 : Certified (graph core0522) (root 10) 0 0 :=
  of_native_maps core0522 DegreeOneSmallSpectrum955.graph DegreeOneSmallSpectrum950.graph
    sourceMap0522 fusedMap0522 sourceMap0522_checked fusedMap0522_checked
    DegreeTwoThreeFiniteComparisons.comparison0522
#print axioms sourceMap0522_checked
#print axioms fusedMap0522_checked
#print axioms certified0522
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
