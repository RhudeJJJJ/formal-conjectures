/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0329 : Family 9 := level9.get ⟨505,by decide⟩
def sourceMap0329 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0329 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,6,7,8,9,10,11,1,2,3,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap0329_checked : acceptsGraphIso
    (source (graph core0329) (root 9) 0 0) DegreeOneSmallSpectrum573.graph sourceMap0329=true := by decide +kernel
theorem fusedMap0329_checked : acceptsGraphIso
    (fused (graph core0329) (root 9) 0 0) DegreeOneSmallSpectrum572.graph fusedMap0329=true := by decide +kernel
theorem certified0329 : Certified (graph core0329) (root 9) 0 0 :=
  of_native_maps core0329 DegreeOneSmallSpectrum573.graph DegreeOneSmallSpectrum572.graph
    sourceMap0329 fusedMap0329 sourceMap0329_checked fusedMap0329_checked
    DegreeTwoThreeFiniteComparisons.comparison0329
#print axioms sourceMap0329_checked
#print axioms fusedMap0329_checked
#print axioms certified0329
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
