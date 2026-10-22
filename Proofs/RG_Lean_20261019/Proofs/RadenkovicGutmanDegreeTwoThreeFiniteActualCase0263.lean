/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0263 : Family 9 := level9.get ⟨345,by decide⟩
def sourceMap0263 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,6,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0263 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,9,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap0263_checked : acceptsGraphIso
    (source (graph core0263) (root 9) 0 0) DegreeTwoThreeSpectrum544.graph sourceMap0263=true := by decide +kernel
theorem fusedMap0263_checked : acceptsGraphIso
    (fused (graph core0263) (root 9) 0 0) DegreeOneSmallSpectrum667.graph fusedMap0263=true := by decide +kernel
theorem certified0263 : Certified (graph core0263) (root 9) 0 0 :=
  of_native_maps core0263 DegreeTwoThreeSpectrum544.graph DegreeOneSmallSpectrum667.graph
    sourceMap0263 fusedMap0263 sourceMap0263_checked fusedMap0263_checked
    DegreeTwoThreeFiniteComparisons.comparison0263
#print axioms sourceMap0263_checked
#print axioms fusedMap0263_checked
#print axioms certified0263
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
