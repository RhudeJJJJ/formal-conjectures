/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0257 : Family 9 := level9.get ⟨327,by decide⟩
def sourceMap0257 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,11,8,9,10] (sourceLabel 9 0 0 v)
def fusedMap0257 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,10,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap0257_checked : acceptsGraphIso
    (source (graph core0257) (root 9) 0 0) DegreeTwoThreeSpectrum525.graph sourceMap0257=true := by decide +kernel
theorem fusedMap0257_checked : acceptsGraphIso
    (fused (graph core0257) (root 9) 0 0) DegreeOneSmallSpectrum623.graph fusedMap0257=true := by decide +kernel
theorem certified0257 : Certified (graph core0257) (root 9) 0 0 :=
  of_native_maps core0257 DegreeTwoThreeSpectrum525.graph DegreeOneSmallSpectrum623.graph
    sourceMap0257 fusedMap0257 sourceMap0257_checked fusedMap0257_checked
    DegreeTwoThreeFiniteComparisons.comparison0257
#print axioms sourceMap0257_checked
#print axioms fusedMap0257_checked
#print axioms certified0257
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
