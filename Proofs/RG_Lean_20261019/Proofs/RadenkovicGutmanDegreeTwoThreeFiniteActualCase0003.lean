/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0003 : Family 4 := level4.get ⟨5,by decide⟩
def sourceMap0003 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 1) → Fin 7 :=
  fun v => ![0,4,5,6,1,2,3] (sourceLabel 4 0 0 v)
def fusedMap0003 : (Vertices 4 ⊕ Fin 2) → Fin 7 :=
  fun v => ![0,1,2,3,6,4,5] (fusedLabel 4 0 0 v)
theorem sourceMap0003_checked : acceptsGraphIso
    (source (graph core0003) (root 4) 0 0) DegreeOneSmallSpectrum011.graph sourceMap0003=true := by decide +kernel
theorem fusedMap0003_checked : acceptsGraphIso
    (fused (graph core0003) (root 4) 0 0) DegreeOneSmallSpectrum014.graph fusedMap0003=true := by decide +kernel
theorem certified0003 : Certified (graph core0003) (root 4) 0 0 :=
  of_native_maps core0003 DegreeOneSmallSpectrum011.graph DegreeOneSmallSpectrum014.graph
    sourceMap0003 fusedMap0003 sourceMap0003_checked fusedMap0003_checked
    DegreeTwoThreeFiniteComparisons.comparison0003
#print axioms sourceMap0003_checked
#print axioms fusedMap0003_checked
#print axioms certified0003
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
