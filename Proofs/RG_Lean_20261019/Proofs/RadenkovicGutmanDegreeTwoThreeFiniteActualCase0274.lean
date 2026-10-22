/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0274 : Family 9 := level9.get ⟨372,by decide⟩
def sourceMap0274 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0274 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0274_checked : acceptsGraphIso
    (source (graph core0274) (root 9) 0 0) DegreeOneSmallSpectrum725.graph sourceMap0274=true := by decide +kernel
theorem fusedMap0274_checked : acceptsGraphIso
    (fused (graph core0274) (root 9) 0 0) DegreeOneSmallSpectrum723.graph fusedMap0274=true := by decide +kernel
theorem certified0274 : Certified (graph core0274) (root 9) 0 0 :=
  of_native_maps core0274 DegreeOneSmallSpectrum725.graph DegreeOneSmallSpectrum723.graph
    sourceMap0274 fusedMap0274 sourceMap0274_checked fusedMap0274_checked
    DegreeTwoThreeFiniteComparisons.comparison0274
#print axioms sourceMap0274_checked
#print axioms fusedMap0274_checked
#print axioms certified0274
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
