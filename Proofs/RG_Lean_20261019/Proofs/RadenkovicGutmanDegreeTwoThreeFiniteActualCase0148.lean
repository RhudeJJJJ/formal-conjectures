/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0148 : Family 8 := level8.get ⟨237,by decide⟩
def sourceMap0148 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,6,7,8,9,10,1,2,3,4,5] (sourceLabel 8 0 0 v)
def fusedMap0148 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,6,7,8,9,10,1,2,3,4,5] (fusedLabel 8 0 0 v)
theorem sourceMap0148_checked : acceptsGraphIso
    (source (graph core0148) (root 8) 0 0) DegreeOneSmallSpectrum288.graph sourceMap0148=true := by decide +kernel
theorem fusedMap0148_checked : acceptsGraphIso
    (fused (graph core0148) (root 8) 0 0) DegreeOneSmallSpectrum278.graph fusedMap0148=true := by decide +kernel
theorem certified0148 : Certified (graph core0148) (root 8) 0 0 :=
  of_native_maps core0148 DegreeOneSmallSpectrum288.graph DegreeOneSmallSpectrum278.graph
    sourceMap0148 fusedMap0148 sourceMap0148_checked fusedMap0148_checked
    DegreeTwoThreeFiniteComparisons.comparison0148
#print axioms sourceMap0148_checked
#print axioms fusedMap0148_checked
#print axioms certified0148
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
