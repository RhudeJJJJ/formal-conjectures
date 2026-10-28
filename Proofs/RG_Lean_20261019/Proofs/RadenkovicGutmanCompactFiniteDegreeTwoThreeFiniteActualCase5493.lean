/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5493 : Family 3 := level3.get ⟨3,by decide⟩
def sourceMap5493 : (Vertices 3 ⊕ Fin 3 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,7,8,9,1,2,3,4,5,6] (sourceLabel 3 2 2 v)
def fusedMap5493 : (Vertices 3 ⊕ Fin 6) → Fin 10 :=
  fun v => ![2,3,4,5,1,0,6,7,8,9] (fusedLabel 3 2 2 v)
theorem sourceMap5493_checked : acceptsGraphIso
    (source (graph core5493) (root 3) 2 2) SmallGeFourSpectrum023.graph sourceMap5493=true := by decide +kernel
theorem fusedMap5493_checked : acceptsGraphIso
    (fused (graph core5493) (root 3) 2 2) DegreeOneSmallSpectrum074.graph fusedMap5493=true := by decide +kernel
theorem certified5493 : Certified (graph core5493) (root 3) 2 2 :=
  of_native_maps core5493 SmallGeFourSpectrum023.graph DegreeOneSmallSpectrum074.graph
    sourceMap5493 fusedMap5493 sourceMap5493_checked fusedMap5493_checked
    DegreeTwoThreeFiniteComparisons.comparison5493
#print axioms sourceMap5493_checked
#print axioms fusedMap5493_checked
#print axioms certified5493
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
