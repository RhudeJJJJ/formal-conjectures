/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0205 : Family 9 := level9.get ⟨181,by decide⟩
def sourceMap0205 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0205 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0205_checked : acceptsGraphIso
    (source (graph core0205) (root 9) 0 0) DegreeOneSmallSpectrum665.graph sourceMap0205=true := by decide +kernel
theorem fusedMap0205_checked : acceptsGraphIso
    (fused (graph core0205) (root 9) 0 0) DegreeOneSmallSpectrum467.graph fusedMap0205=true := by decide +kernel
theorem certified0205 : Certified (graph core0205) (root 9) 0 0 :=
  of_native_maps core0205 DegreeOneSmallSpectrum665.graph DegreeOneSmallSpectrum467.graph
    sourceMap0205 fusedMap0205 sourceMap0205_checked fusedMap0205_checked
    DegreeTwoThreeFiniteComparisons.comparison0205
#print axioms sourceMap0205_checked
#print axioms fusedMap0205_checked
#print axioms certified0205
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
