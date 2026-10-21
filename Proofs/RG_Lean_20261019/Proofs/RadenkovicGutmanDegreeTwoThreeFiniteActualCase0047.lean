/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0047 : Family 7 := level7.get ⟨67,by decide⟩
def sourceMap0047 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![1,0,5,6,7,8,9,2,3,4] (sourceLabel 7 0 0 v)
def fusedMap0047 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,9,7,8] (fusedLabel 7 0 0 v)
theorem sourceMap0047_checked : acceptsGraphIso
    (source (graph core0047) (root 7) 0 0) DegreeTwoThreeSpectrum145.graph sourceMap0047=true := by decide +kernel
theorem fusedMap0047_checked : acceptsGraphIso
    (fused (graph core0047) (root 7) 0 0) DegreeOneSmallSpectrum100.graph fusedMap0047=true := by decide +kernel
theorem certified0047 : Certified (graph core0047) (root 7) 0 0 :=
  of_native_maps core0047 DegreeTwoThreeSpectrum145.graph DegreeOneSmallSpectrum100.graph
    sourceMap0047 fusedMap0047 sourceMap0047_checked fusedMap0047_checked
    DegreeTwoThreeFiniteComparisons.comparison0047
#print axioms sourceMap0047_checked
#print axioms fusedMap0047_checked
#print axioms certified0047
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
