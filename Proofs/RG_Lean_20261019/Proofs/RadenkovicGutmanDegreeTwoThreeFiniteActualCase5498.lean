/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5498 : Family 6 := level6.get ⟨18,by decide⟩
def sourceMap5498 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,9,10,11,12,7,8,1,2,3,4,5,6] (sourceLabel 6 2 2 v)
def fusedMap5498 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap5498_checked : acceptsGraphIso
    (source (graph core5498) (root 6) 2 2) DegreeOneSmallSpectrum1457.graph sourceMap5498=true := by decide +kernel
theorem fusedMap5498_checked : acceptsGraphIso
    (fused (graph core5498) (root 6) 2 2) DegreeOneSmallSpectrum974.graph fusedMap5498=true := by decide +kernel
theorem certified5498 : Certified (graph core5498) (root 6) 2 2 :=
  of_native_maps core5498 DegreeOneSmallSpectrum1457.graph DegreeOneSmallSpectrum974.graph
    sourceMap5498 fusedMap5498 sourceMap5498_checked fusedMap5498_checked
    DegreeTwoThreeFiniteComparisons.comparison5498
#print axioms sourceMap5498_checked
#print axioms fusedMap5498_checked
#print axioms certified5498
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
