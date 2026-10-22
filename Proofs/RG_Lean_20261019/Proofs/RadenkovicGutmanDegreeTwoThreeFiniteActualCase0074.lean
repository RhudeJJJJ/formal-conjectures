/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0074 : Family 8 := level8.get ⟨50,by decide⟩
def sourceMap0074 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,7,8,9,10,6,3,4,5] (sourceLabel 8 0 0 v)
def fusedMap0074 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,5,0,1,2,3,4,10,9,7,8] (fusedLabel 8 0 0 v)
theorem sourceMap0074_checked : acceptsGraphIso
    (source (graph core0074) (root 8) 0 0) DegreeOneSmallSpectrum255.graph sourceMap0074=true := by decide +kernel
theorem fusedMap0074_checked : acceptsGraphIso
    (fused (graph core0074) (root 8) 0 0) DegreeOneSmallSpectrum192.graph fusedMap0074=true := by decide +kernel
theorem certified0074 : Certified (graph core0074) (root 8) 0 0 :=
  of_native_maps core0074 DegreeOneSmallSpectrum255.graph DegreeOneSmallSpectrum192.graph
    sourceMap0074 fusedMap0074 sourceMap0074_checked fusedMap0074_checked
    DegreeTwoThreeFiniteComparisons.comparison0074
#print axioms sourceMap0074_checked
#print axioms fusedMap0074_checked
#print axioms certified0074
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
