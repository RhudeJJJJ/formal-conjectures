/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0215 : Family 9 := level9.get ⟨210,by decide⟩
def sourceMap0215 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0215 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,11,10,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap0215_checked : acceptsGraphIso
    (source (graph core0215) (root 9) 0 0) DegreeOneSmallSpectrum654.graph sourceMap0215=true := by decide +kernel
theorem fusedMap0215_checked : acceptsGraphIso
    (fused (graph core0215) (root 9) 0 0) DegreeOneSmallSpectrum513.graph fusedMap0215=true := by decide +kernel
theorem certified0215 : Certified (graph core0215) (root 9) 0 0 :=
  of_native_maps core0215 DegreeOneSmallSpectrum654.graph DegreeOneSmallSpectrum513.graph
    sourceMap0215 fusedMap0215 sourceMap0215_checked fusedMap0215_checked
    DegreeTwoThreeFiniteComparisons.comparison0215
#print axioms sourceMap0215_checked
#print axioms fusedMap0215_checked
#print axioms certified0215
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
