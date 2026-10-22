/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0106 : Family 8 := level8.get ⟨143,by decide⟩
def sourceMap0106 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,2,3,4] (sourceLabel 8 0 0 v)
def fusedMap0106 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0106_checked : acceptsGraphIso
    (source (graph core0106) (root 8) 0 0) SmallGeFourSpectrum046.graph sourceMap0106=true := by decide +kernel
theorem fusedMap0106_checked : acceptsGraphIso
    (fused (graph core0106) (root 8) 0 0) SmallGeFourSpectrum064.graph fusedMap0106=true := by decide +kernel
theorem certified0106 : Certified (graph core0106) (root 8) 0 0 :=
  of_native_maps core0106 SmallGeFourSpectrum046.graph SmallGeFourSpectrum064.graph
    sourceMap0106 fusedMap0106 sourceMap0106_checked fusedMap0106_checked
    DegreeTwoThreeFiniteComparisons.comparison0106
#print axioms sourceMap0106_checked
#print axioms fusedMap0106_checked
#print axioms certified0106
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
