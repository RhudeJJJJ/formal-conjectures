/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0111 : Family 8 := level8.get ⟨155,by decide⟩
def sourceMap0111 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,2,3,4,5] (sourceLabel 8 0 0 v)
def fusedMap0111 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,2,3,4,5] (fusedLabel 8 0 0 v)
theorem sourceMap0111_checked : acceptsGraphIso
    (source (graph core0111) (root 8) 0 0) DegreeOneSmallSpectrum336.graph sourceMap0111=true := by decide +kernel
theorem fusedMap0111_checked : acceptsGraphIso
    (fused (graph core0111) (root 8) 0 0) DegreeOneSmallSpectrum328.graph fusedMap0111=true := by decide +kernel
theorem certified0111 : Certified (graph core0111) (root 8) 0 0 :=
  of_native_maps core0111 DegreeOneSmallSpectrum336.graph DegreeOneSmallSpectrum328.graph
    sourceMap0111 fusedMap0111 sourceMap0111_checked fusedMap0111_checked
    DegreeTwoThreeFiniteComparisons.comparison0111
#print axioms sourceMap0111_checked
#print axioms fusedMap0111_checked
#print axioms certified0111
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
