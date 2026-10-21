/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0009 : Family 5 := level5.get ⟨14,by decide⟩
def sourceMap0009 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 1) → Fin 8 :=
  fun v => ![0,4,5,6,7,1,2,3] (sourceLabel 5 0 0 v)
def fusedMap0009 : (Vertices 5 ⊕ Fin 2) → Fin 8 :=
  fun v => ![0,1,2,3,4,7,5,6] (fusedLabel 5 0 0 v)
theorem sourceMap0009_checked : acceptsGraphIso
    (source (graph core0009) (root 5) 0 0) DegreeTwoThreeSpectrum025.graph sourceMap0009=true := by decide +kernel
theorem fusedMap0009_checked : acceptsGraphIso
    (fused (graph core0009) (root 5) 0 0) DegreeOneSmallSpectrum030.graph fusedMap0009=true := by decide +kernel
theorem certified0009 : Certified (graph core0009) (root 5) 0 0 :=
  of_native_maps core0009 DegreeTwoThreeSpectrum025.graph DegreeOneSmallSpectrum030.graph
    sourceMap0009 fusedMap0009 sourceMap0009_checked fusedMap0009_checked
    DegreeTwoThreeFiniteComparisons.comparison0009
#print axioms sourceMap0009_checked
#print axioms fusedMap0009_checked
#print axioms certified0009
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
