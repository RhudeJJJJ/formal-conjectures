/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0512 : Family 10 := level10.get ⟨437,by decide⟩
def sourceMap0512 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,6,7,8,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0512 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0512_checked : acceptsGraphIso
    (source (graph core0512) (root 10) 0 0) DegreeOneSmallSpectrum1039.graph sourceMap0512=true := by decide +kernel
theorem fusedMap0512_checked : acceptsGraphIso
    (fused (graph core0512) (root 10) 0 0) DegreeOneSmallSpectrum1453.graph fusedMap0512=true := by decide +kernel
theorem certified0512 : Certified (graph core0512) (root 10) 0 0 :=
  of_native_maps core0512 DegreeOneSmallSpectrum1039.graph DegreeOneSmallSpectrum1453.graph
    sourceMap0512 fusedMap0512 sourceMap0512_checked fusedMap0512_checked
    DegreeTwoThreeFiniteComparisons.comparison0512
#print axioms sourceMap0512_checked
#print axioms fusedMap0512_checked
#print axioms certified0512
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
