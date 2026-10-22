/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0476 : Family 10 := level10.get ⟨320,by decide⟩
def sourceMap0476 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0476 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0476_checked : acceptsGraphIso
    (source (graph core0476) (root 10) 0 0) DegreeTwoThreeSpectrum871.graph sourceMap0476=true := by decide +kernel
theorem fusedMap0476_checked : acceptsGraphIso
    (fused (graph core0476) (root 10) 0 0) DegreeOneSmallSpectrum1383.graph fusedMap0476=true := by decide +kernel
theorem certified0476 : Certified (graph core0476) (root 10) 0 0 :=
  of_native_maps core0476 DegreeTwoThreeSpectrum871.graph DegreeOneSmallSpectrum1383.graph
    sourceMap0476 fusedMap0476 sourceMap0476_checked fusedMap0476_checked
    DegreeTwoThreeFiniteComparisons.comparison0476
#print axioms sourceMap0476_checked
#print axioms fusedMap0476_checked
#print axioms certified0476
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
