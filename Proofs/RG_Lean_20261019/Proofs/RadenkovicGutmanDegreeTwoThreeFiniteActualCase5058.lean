/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5058 : Family 4 := level4.get ⟨5,by decide⟩
def sourceMap5058 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,5,6,7,8,2,3,4,0,9,10,11,12] (sourceLabel 4 2 4 v)
def fusedMap5058 : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12] (fusedLabel 4 2 4 v)
theorem sourceMap5058_checked : acceptsGraphIso
    (source (graph core5058) (root 4) 2 4) DegreeOneSmallSpectrum1471.graph sourceMap5058=true := by decide +kernel
theorem fusedMap5058_checked : acceptsGraphIso
    (fused (graph core5058) (root 4) 2 4) DegreeOneSmallSpectrum879.graph fusedMap5058=true := by decide +kernel
theorem certified5058 : Certified (graph core5058) (root 4) 2 4 :=
  of_native_maps core5058 DegreeOneSmallSpectrum1471.graph DegreeOneSmallSpectrum879.graph
    sourceMap5058 fusedMap5058 sourceMap5058_checked fusedMap5058_checked
    DegreeTwoThreeFiniteComparisons.comparison5058
#print axioms sourceMap5058_checked
#print axioms fusedMap5058_checked
#print axioms certified5058
def sourceMap5058swap : (Vertices 4 ⊕ Fin 5 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,5,6,7,8,0,9,10,11,12,2,3,4] (sourceLabel 4 4 2 v)
def fusedMap5058swap : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12] (fusedLabel 4 4 2 v)
theorem sourceMap5058swap_checked : acceptsGraphIso
    (source (graph core5058) (root 4) 4 2) DegreeOneSmallSpectrum1471.graph sourceMap5058swap=true := by decide +kernel
theorem fusedMap5058swap_checked : acceptsGraphIso
    (fused (graph core5058) (root 4) 4 2) DegreeOneSmallSpectrum879.graph fusedMap5058swap=true := by decide +kernel
theorem certified5058swap : Certified (graph core5058) (root 4) 4 2 :=
  of_native_maps core5058 DegreeOneSmallSpectrum1471.graph DegreeOneSmallSpectrum879.graph
    sourceMap5058swap fusedMap5058swap sourceMap5058swap_checked fusedMap5058swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5058
#print axioms sourceMap5058swap_checked
#print axioms fusedMap5058swap_checked
#print axioms certified5058swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
