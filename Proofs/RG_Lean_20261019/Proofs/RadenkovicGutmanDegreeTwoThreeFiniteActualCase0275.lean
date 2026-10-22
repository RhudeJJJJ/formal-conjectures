/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0275 : Family 9 := level9.get ⟨377,by decide⟩
def sourceMap0275 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,5,6,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0275 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,9,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap0275_checked : acceptsGraphIso
    (source (graph core0275) (root 9) 0 0) DegreeOneSmallSpectrum636.graph sourceMap0275=true := by decide +kernel
theorem fusedMap0275_checked : acceptsGraphIso
    (fused (graph core0275) (root 9) 0 0) DegreeOneSmallSpectrum739.graph fusedMap0275=true := by decide +kernel
theorem certified0275 : Certified (graph core0275) (root 9) 0 0 :=
  of_native_maps core0275 DegreeOneSmallSpectrum636.graph DegreeOneSmallSpectrum739.graph
    sourceMap0275 fusedMap0275 sourceMap0275_checked fusedMap0275_checked
    DegreeTwoThreeFiniteComparisons.comparison0275
#print axioms sourceMap0275_checked
#print axioms fusedMap0275_checked
#print axioms certified0275
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
