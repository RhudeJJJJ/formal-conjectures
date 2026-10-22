/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0447 : Family 10 := level10.get ⟨213,by decide⟩
def sourceMap0447 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0447 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0447_checked : acceptsGraphIso
    (source (graph core0447) (root 10) 0 0) DegreeTwoThreeSpectrum916.graph sourceMap0447=true := by decide +kernel
theorem fusedMap0447_checked : acceptsGraphIso
    (fused (graph core0447) (root 10) 0 0) DegreeOneSmallSpectrum1069.graph fusedMap0447=true := by decide +kernel
theorem certified0447 : Certified (graph core0447) (root 10) 0 0 :=
  of_native_maps core0447 DegreeTwoThreeSpectrum916.graph DegreeOneSmallSpectrum1069.graph
    sourceMap0447 fusedMap0447 sourceMap0447_checked fusedMap0447_checked
    DegreeTwoThreeFiniteComparisons.comparison0447
#print axioms sourceMap0447_checked
#print axioms fusedMap0447_checked
#print axioms certified0447
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
