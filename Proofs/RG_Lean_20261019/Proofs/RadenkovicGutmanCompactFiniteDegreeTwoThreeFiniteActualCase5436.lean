/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5436 : Family 6 := level6.get ⟨42,by decide⟩
def sourceMap5436 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (sourceLabel 6 0 0 v)
def fusedMap5436 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,8,6,7] (fusedLabel 6 0 0 v)
theorem sourceMap5436_checked : acceptsGraphIso
    (source (graph core5436) (root 6) 0 0) SmallGeFourSpectrum011.graph sourceMap5436=true := by decide +kernel
theorem fusedMap5436_checked : acceptsGraphIso
    (fused (graph core5436) (root 6) 0 0) DegreeOneSmallSpectrum071.graph fusedMap5436=true := by decide +kernel
theorem certified5436 : Certified (graph core5436) (root 6) 0 0 :=
  of_native_maps core5436 SmallGeFourSpectrum011.graph DegreeOneSmallSpectrum071.graph
    sourceMap5436 fusedMap5436 sourceMap5436_checked fusedMap5436_checked
    DegreeTwoThreeFiniteComparisons.comparison5436
#print axioms sourceMap5436_checked
#print axioms fusedMap5436_checked
#print axioms certified5436
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
