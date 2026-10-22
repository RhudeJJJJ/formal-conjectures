/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0144 : Family 8 := level8.get ⟨231,by decide⟩
def sourceMap0144 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,2,3,4] (sourceLabel 8 0 0 v)
def fusedMap0144 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0144_checked : acceptsGraphIso
    (source (graph core0144) (root 8) 0 0) DegreeTwoThreeSpectrum324.graph sourceMap0144=true := by decide +kernel
theorem fusedMap0144_checked : acceptsGraphIso
    (fused (graph core0144) (root 8) 0 0) DegreeOneSmallSpectrum317.graph fusedMap0144=true := by decide +kernel
theorem certified0144 : Certified (graph core0144) (root 8) 0 0 :=
  of_native_maps core0144 DegreeTwoThreeSpectrum324.graph DegreeOneSmallSpectrum317.graph
    sourceMap0144 fusedMap0144 sourceMap0144_checked fusedMap0144_checked
    DegreeTwoThreeFiniteComparisons.comparison0144
#print axioms sourceMap0144_checked
#print axioms fusedMap0144_checked
#print axioms certified0144
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
