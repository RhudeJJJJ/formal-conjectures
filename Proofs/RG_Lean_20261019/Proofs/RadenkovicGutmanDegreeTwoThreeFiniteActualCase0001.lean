/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0001 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap0001 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 1) → Fin 6 :=
  fun v => ![0,4,5,1,2,3] (sourceLabel 3 0 0 v)
def fusedMap0001 : (Vertices 3 ⊕ Fin 2) → Fin 6 :=
  fun v => ![0,1,2,5,3,4] (fusedLabel 3 0 0 v)
theorem sourceMap0001_checked : acceptsGraphIso
    (source (graph core0001) (root 3) 0 0) DegreeTwoThreeSpectrum002.graph sourceMap0001=true := by decide +kernel
theorem fusedMap0001_checked : acceptsGraphIso
    (fused (graph core0001) (root 3) 0 0) DegreeOneSmallSpectrum007.graph fusedMap0001=true := by decide +kernel
theorem certified0001 : Certified (graph core0001) (root 3) 0 0 :=
  of_native_maps core0001 DegreeTwoThreeSpectrum002.graph DegreeOneSmallSpectrum007.graph
    sourceMap0001 fusedMap0001 sourceMap0001_checked fusedMap0001_checked
    DegreeTwoThreeFiniteComparisons.comparison0001
#print axioms sourceMap0001_checked
#print axioms fusedMap0001_checked
#print axioms certified0001
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
