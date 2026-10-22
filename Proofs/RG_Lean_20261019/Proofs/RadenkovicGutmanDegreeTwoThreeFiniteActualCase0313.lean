/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0313 : Family 9 := level9.get ⟨470,by decide⟩
def sourceMap0313 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,5,6,7,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0313 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,4,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap0313_checked : acceptsGraphIso
    (source (graph core0313) (root 9) 0 0) DegreeOneSmallSpectrum643.graph sourceMap0313=true := by decide +kernel
theorem fusedMap0313_checked : acceptsGraphIso
    (fused (graph core0313) (root 9) 0 0) DegreeOneSmallSpectrum815.graph fusedMap0313=true := by decide +kernel
theorem certified0313 : Certified (graph core0313) (root 9) 0 0 :=
  of_native_maps core0313 DegreeOneSmallSpectrum643.graph DegreeOneSmallSpectrum815.graph
    sourceMap0313 fusedMap0313 sourceMap0313_checked fusedMap0313_checked
    DegreeTwoThreeFiniteComparisons.comparison0313
#print axioms sourceMap0313_checked
#print axioms fusedMap0313_checked
#print axioms certified0313
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
