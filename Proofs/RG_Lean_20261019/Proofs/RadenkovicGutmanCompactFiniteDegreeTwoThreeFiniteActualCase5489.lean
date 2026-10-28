/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5489 : Family 3 := level3.get ⟨3,by decide⟩
def sourceMap5489 : (Vertices 3 ⊕ Fin 2 ⊕ Fin 2) → Fin 8 :=
  fun v => ![0,5,6,7,1,2,3,4] (sourceLabel 3 1 1 v)
def fusedMap5489 : (Vertices 3 ⊕ Fin 4) → Fin 8 :=
  fun v => ![1,2,3,4,0,5,6,7] (fusedLabel 3 1 1 v)
theorem sourceMap5489_checked : acceptsGraphIso
    (source (graph core5489) (root 3) 1 1) SmallGeFourSpectrum004.graph sourceMap5489=true := by decide +kernel
theorem fusedMap5489_checked : acceptsGraphIso
    (fused (graph core5489) (root 3) 1 1) DegreeOneSmallSpectrum017.graph fusedMap5489=true := by decide +kernel
theorem certified5489 : Certified (graph core5489) (root 3) 1 1 :=
  of_native_maps core5489 SmallGeFourSpectrum004.graph DegreeOneSmallSpectrum017.graph
    sourceMap5489 fusedMap5489 sourceMap5489_checked fusedMap5489_checked
    DegreeTwoThreeFiniteComparisons.comparison5489
#print axioms sourceMap5489_checked
#print axioms fusedMap5489_checked
#print axioms certified5489
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
