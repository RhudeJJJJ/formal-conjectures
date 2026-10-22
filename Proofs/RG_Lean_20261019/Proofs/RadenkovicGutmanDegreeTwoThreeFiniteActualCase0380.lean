/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0380 : Family 9 := level9.get ⟨632,by decide⟩
def sourceMap0380 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0380 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0380_checked : acceptsGraphIso
    (source (graph core0380) (root 9) 0 0) DegreeTwoThreeSpectrum651.graph sourceMap0380=true := by decide +kernel
theorem fusedMap0380_checked : acceptsGraphIso
    (fused (graph core0380) (root 9) 0 0) DegreeOneSmallSpectrum775.graph fusedMap0380=true := by decide +kernel
theorem certified0380 : Certified (graph core0380) (root 9) 0 0 :=
  of_native_maps core0380 DegreeTwoThreeSpectrum651.graph DegreeOneSmallSpectrum775.graph
    sourceMap0380 fusedMap0380 sourceMap0380_checked fusedMap0380_checked
    DegreeTwoThreeFiniteComparisons.comparison0380
#print axioms sourceMap0380_checked
#print axioms fusedMap0380_checked
#print axioms certified0380
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
