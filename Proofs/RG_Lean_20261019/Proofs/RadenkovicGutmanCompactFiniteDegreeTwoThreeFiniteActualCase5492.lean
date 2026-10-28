/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5492 : Family 3 := level3.get ⟨3,by decide⟩
def sourceMap5492 : (Vertices 3 ⊕ Fin 2 ⊕ Fin 6) → Fin 12 :=
  fun v => ![2,5,6,7,3,4,1,0,8,9,10,11] (sourceLabel 3 1 5 v)
def fusedMap5492 : (Vertices 3 ⊕ Fin 8) → Fin 12 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11] (fusedLabel 3 1 5 v)
theorem sourceMap5492_checked : acceptsGraphIso
    (source (graph core5492) (root 3) 1 5) SmallGeFourSpectrum104.graph sourceMap5492=true := by decide +kernel
theorem fusedMap5492_checked : acceptsGraphIso
    (fused (graph core5492) (root 3) 1 5) DegreeOneSmallSpectrum370.graph fusedMap5492=true := by decide +kernel
theorem certified5492 : Certified (graph core5492) (root 3) 1 5 :=
  of_native_maps core5492 SmallGeFourSpectrum104.graph DegreeOneSmallSpectrum370.graph
    sourceMap5492 fusedMap5492 sourceMap5492_checked fusedMap5492_checked
    DegreeTwoThreeFiniteComparisons.comparison5492
#print axioms sourceMap5492_checked
#print axioms fusedMap5492_checked
#print axioms certified5492
def sourceMap5492swap : (Vertices 3 ⊕ Fin 6 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,5,6,7,1,0,8,9,10,11,3,4] (sourceLabel 3 5 1 v)
def fusedMap5492swap : (Vertices 3 ⊕ Fin 8) → Fin 12 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11] (fusedLabel 3 5 1 v)
theorem sourceMap5492swap_checked : acceptsGraphIso
    (source (graph core5492) (root 3) 5 1) SmallGeFourSpectrum104.graph sourceMap5492swap=true := by decide +kernel
theorem fusedMap5492swap_checked : acceptsGraphIso
    (fused (graph core5492) (root 3) 5 1) DegreeOneSmallSpectrum370.graph fusedMap5492swap=true := by decide +kernel
theorem certified5492swap : Certified (graph core5492) (root 3) 5 1 :=
  of_native_maps core5492 SmallGeFourSpectrum104.graph DegreeOneSmallSpectrum370.graph
    sourceMap5492swap fusedMap5492swap sourceMap5492swap_checked fusedMap5492swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5492
#print axioms sourceMap5492swap_checked
#print axioms fusedMap5492swap_checked
#print axioms certified5492swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
