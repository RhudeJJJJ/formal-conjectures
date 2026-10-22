/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0104 : Family 8 := level8.get ⟨138,by decide⟩
def sourceMap0104 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,5,2,3,4] (sourceLabel 8 0 0 v)
def fusedMap0104 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,10,9,7,8] (fusedLabel 8 0 0 v)
theorem sourceMap0104_checked : acceptsGraphIso
    (source (graph core0104) (root 8) 0 0) DegreeOneSmallSpectrum256.graph sourceMap0104=true := by decide +kernel
theorem fusedMap0104_checked : acceptsGraphIso
    (fused (graph core0104) (root 8) 0 0) DegreeOneSmallSpectrum328.graph fusedMap0104=true := by decide +kernel
theorem certified0104 : Certified (graph core0104) (root 8) 0 0 :=
  of_native_maps core0104 DegreeOneSmallSpectrum256.graph DegreeOneSmallSpectrum328.graph
    sourceMap0104 fusedMap0104 sourceMap0104_checked fusedMap0104_checked
    DegreeTwoThreeFiniteComparisons.comparison0104
#print axioms sourceMap0104_checked
#print axioms fusedMap0104_checked
#print axioms certified0104
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
