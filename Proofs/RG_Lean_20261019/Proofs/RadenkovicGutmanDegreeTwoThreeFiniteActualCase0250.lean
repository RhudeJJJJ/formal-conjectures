/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0250 : Family 9 := level9.get ⟨305,by decide⟩
def sourceMap0250 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,7,2,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0250 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,7,2,3,4,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap0250_checked : acceptsGraphIso
    (source (graph core0250) (root 9) 0 0) DegreeOneSmallSpectrum436.graph sourceMap0250=true := by decide +kernel
theorem fusedMap0250_checked : acceptsGraphIso
    (fused (graph core0250) (root 9) 0 0) DegreeOneSmallSpectrum430.graph fusedMap0250=true := by decide +kernel
theorem certified0250 : Certified (graph core0250) (root 9) 0 0 :=
  of_native_maps core0250 DegreeOneSmallSpectrum436.graph DegreeOneSmallSpectrum430.graph
    sourceMap0250 fusedMap0250 sourceMap0250_checked fusedMap0250_checked
    DegreeTwoThreeFiniteComparisons.comparison0250
#print axioms sourceMap0250_checked
#print axioms fusedMap0250_checked
#print axioms certified0250
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
