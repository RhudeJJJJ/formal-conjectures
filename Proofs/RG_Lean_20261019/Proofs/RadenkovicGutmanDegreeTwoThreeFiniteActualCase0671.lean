/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0671 : Family 10 := level10.get ⟨889,by decide⟩
def sourceMap0671 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,6,2,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0671 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,6,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0671_checked : acceptsGraphIso
    (source (graph core0671) (root 10) 0 0) DegreeOneSmallSpectrum1378.graph sourceMap0671=true := by decide +kernel
theorem fusedMap0671_checked : acceptsGraphIso
    (fused (graph core0671) (root 10) 0 0) DegreeOneSmallSpectrum1329.graph fusedMap0671=true := by decide +kernel
theorem certified0671 : Certified (graph core0671) (root 10) 0 0 :=
  of_native_maps core0671 DegreeOneSmallSpectrum1378.graph DegreeOneSmallSpectrum1329.graph
    sourceMap0671 fusedMap0671 sourceMap0671_checked fusedMap0671_checked
    DegreeTwoThreeFiniteComparisons.comparison0671
#print axioms sourceMap0671_checked
#print axioms fusedMap0671_checked
#print axioms certified0671
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
