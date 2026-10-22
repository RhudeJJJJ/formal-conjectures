/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0252 : Family 9 := level9.get ⟨309,by decide⟩
def sourceMap0252 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,2,3,4,5,6,7] (sourceLabel 9 0 0 v)
def fusedMap0252 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,2,3,4,5,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap0252_checked : acceptsGraphIso
    (source (graph core0252) (root 9) 0 0) DegreeOneSmallSpectrum469.graph sourceMap0252=true := by decide +kernel
theorem fusedMap0252_checked : acceptsGraphIso
    (fused (graph core0252) (root 9) 0 0) DegreeOneSmallSpectrum464.graph fusedMap0252=true := by decide +kernel
theorem certified0252 : Certified (graph core0252) (root 9) 0 0 :=
  of_native_maps core0252 DegreeOneSmallSpectrum469.graph DegreeOneSmallSpectrum464.graph
    sourceMap0252 fusedMap0252 sourceMap0252_checked fusedMap0252_checked
    DegreeTwoThreeFiniteComparisons.comparison0252
#print axioms sourceMap0252_checked
#print axioms fusedMap0252_checked
#print axioms certified0252
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
