/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0127 : Family 8 := level8.get ⟨193,by decide⟩
def sourceMap0127 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,10,7,8,9] (sourceLabel 8 0 0 v)
def fusedMap0127 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0127_checked : acceptsGraphIso
    (source (graph core0127) (root 8) 0 0) DegreeTwoThreeSpectrum316.graph sourceMap0127=true := by decide +kernel
theorem fusedMap0127_checked : acceptsGraphIso
    (fused (graph core0127) (root 8) 0 0) DegreeOneSmallSpectrum238.graph fusedMap0127=true := by decide +kernel
theorem certified0127 : Certified (graph core0127) (root 8) 0 0 :=
  of_native_maps core0127 DegreeTwoThreeSpectrum316.graph DegreeOneSmallSpectrum238.graph
    sourceMap0127 fusedMap0127 sourceMap0127_checked fusedMap0127_checked
    DegreeTwoThreeFiniteComparisons.comparison0127
#print axioms sourceMap0127_checked
#print axioms fusedMap0127_checked
#print axioms certified0127
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
