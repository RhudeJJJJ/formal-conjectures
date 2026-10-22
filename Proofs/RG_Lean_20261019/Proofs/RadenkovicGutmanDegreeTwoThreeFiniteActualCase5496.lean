/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5496 : Family 5 := level5.get ⟨16,by decide⟩
def sourceMap5496 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,7,8,9,10,11,1,2,3,4,5,6] (sourceLabel 5 2 2 v)
def fusedMap5496 : (Vertices 5 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11] (fusedLabel 5 2 2 v)
theorem sourceMap5496_checked : acceptsGraphIso
    (source (graph core5496) (root 5) 2 2) SmallGeFourSpectrum193.graph sourceMap5496=true := by decide +kernel
theorem fusedMap5496_checked : acceptsGraphIso
    (fused (graph core5496) (root 5) 2 2) DegreeOneSmallSpectrum440.graph fusedMap5496=true := by decide +kernel
theorem certified5496 : Certified (graph core5496) (root 5) 2 2 :=
  of_native_maps core5496 SmallGeFourSpectrum193.graph DegreeOneSmallSpectrum440.graph
    sourceMap5496 fusedMap5496 sourceMap5496_checked fusedMap5496_checked
    DegreeTwoThreeFiniteComparisons.comparison5496
#print axioms sourceMap5496_checked
#print axioms fusedMap5496_checked
#print axioms certified5496
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
