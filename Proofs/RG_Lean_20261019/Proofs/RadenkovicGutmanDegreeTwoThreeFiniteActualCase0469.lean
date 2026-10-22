/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0469 : Family 10 := level10.get ⟨294,by decide⟩
def sourceMap0469 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0469 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0469_checked : acceptsGraphIso
    (source (graph core0469) (root 10) 0 0) DegreeOneSmallSpectrum1068.graph sourceMap0469=true := by decide +kernel
theorem fusedMap0469_checked : acceptsGraphIso
    (fused (graph core0469) (root 10) 0 0) DegreeOneSmallSpectrum1327.graph fusedMap0469=true := by decide +kernel
theorem certified0469 : Certified (graph core0469) (root 10) 0 0 :=
  of_native_maps core0469 DegreeOneSmallSpectrum1068.graph DegreeOneSmallSpectrum1327.graph
    sourceMap0469 fusedMap0469 sourceMap0469_checked fusedMap0469_checked
    DegreeTwoThreeFiniteComparisons.comparison0469
#print axioms sourceMap0469_checked
#print axioms fusedMap0469_checked
#print axioms certified0469
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
