/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3749 : Family 4 := level4.get ⟨6,by decide⟩
def sourceMap3749 : (Vertices 4 ⊕ Fin 2 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (sourceLabel 4 1 1 v)
def fusedMap3749 : (Vertices 4 ⊕ Fin 4) → Fin 9 :=
  fun v => ![1,2,3,4,5,0,6,7,8] (fusedLabel 4 1 1 v)
theorem sourceMap3749_checked : acceptsGraphIso
    (source (graph core3749) (root 4) 1 1) DegreeTwoThreeSpectrum069.graph sourceMap3749=true := by decide +kernel
theorem fusedMap3749_checked : acceptsGraphIso
    (fused (graph core3749) (root 4) 1 1) DegreeOneSmallSpectrum055.graph fusedMap3749=true := by decide +kernel
theorem certified3749 : Certified (graph core3749) (root 4) 1 1 :=
  of_native_maps core3749 DegreeTwoThreeSpectrum069.graph DegreeOneSmallSpectrum055.graph
    sourceMap3749 fusedMap3749 sourceMap3749_checked fusedMap3749_checked
    DegreeTwoThreeFiniteComparisons.comparison3749
#print axioms sourceMap3749_checked
#print axioms fusedMap3749_checked
#print axioms certified3749
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
