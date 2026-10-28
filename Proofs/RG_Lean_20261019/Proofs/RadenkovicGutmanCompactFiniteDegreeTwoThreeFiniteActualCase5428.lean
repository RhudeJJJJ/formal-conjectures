/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons108
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5428 : Family 5 := level5.get ⟨12,by decide⟩
def sourceMap5428 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 1) → Fin 8 :=
  fun v => ![1,0,6,7,2,3,4,5] (sourceLabel 5 0 0 v)
def fusedMap5428 : (Vertices 5 ⊕ Fin 2) → Fin 8 :=
  fun v => ![0,5,6,7,3,4,1,2] (fusedLabel 5 0 0 v)
theorem sourceMap5428_checked : acceptsGraphIso
    (source (graph core5428) (root 5) 0 0) SmallGeFourSpectrum003.graph sourceMap5428=true := by decide +kernel
theorem fusedMap5428_checked : acceptsGraphIso
    (fused (graph core5428) (root 5) 0 0) DegreeOneSmallSpectrum023.graph fusedMap5428=true := by decide +kernel
theorem certified5428 : Certified (graph core5428) (root 5) 0 0 :=
  of_native_maps core5428 SmallGeFourSpectrum003.graph DegreeOneSmallSpectrum023.graph
    sourceMap5428 fusedMap5428 sourceMap5428_checked fusedMap5428_checked
    DegreeTwoThreeFiniteComparisons.comparison5428
#print axioms sourceMap5428_checked
#print axioms fusedMap5428_checked
#print axioms certified5428
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
