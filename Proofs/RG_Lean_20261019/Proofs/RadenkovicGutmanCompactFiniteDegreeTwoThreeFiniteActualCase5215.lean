/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5215 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap5215 : (Vertices 2 ⊕ Fin 3 ⊕ Fin 6) → Fin 12 :=
  fun v => ![1,5,6,2,3,4,0,7,8,9,10,11] (sourceLabel 2 2 5 v)
def fusedMap5215 : (Vertices 2 ⊕ Fin 9) → Fin 12 :=
  fun v => ![4,5,6,3,2,1,0,7,8,9,10,11] (fusedLabel 2 2 5 v)
theorem sourceMap5215_checked : acceptsGraphIso
    (source (graph core5215) (root 2) 2 5) DegreeOneSmallSpectrum388.graph sourceMap5215=true := by decide +kernel
theorem fusedMap5215_checked : acceptsGraphIso
    (fused (graph core5215) (root 2) 2 5) DegreeOneSmallSpectrum378.graph fusedMap5215=true := by decide +kernel
theorem certified5215 : Certified (graph core5215) (root 2) 2 5 :=
  of_native_maps core5215 DegreeOneSmallSpectrum388.graph DegreeOneSmallSpectrum378.graph
    sourceMap5215 fusedMap5215 sourceMap5215_checked fusedMap5215_checked
    DegreeTwoThreeFiniteComparisons.comparison5215
#print axioms sourceMap5215_checked
#print axioms fusedMap5215_checked
#print axioms certified5215
def sourceMap5215swap : (Vertices 2 ⊕ Fin 6 ⊕ Fin 3) → Fin 12 :=
  fun v => ![1,5,6,0,7,8,9,10,11,2,3,4] (sourceLabel 2 5 2 v)
def fusedMap5215swap : (Vertices 2 ⊕ Fin 9) → Fin 12 :=
  fun v => ![4,5,6,3,2,1,0,7,8,9,10,11] (fusedLabel 2 5 2 v)
theorem sourceMap5215swap_checked : acceptsGraphIso
    (source (graph core5215) (root 2) 5 2) DegreeOneSmallSpectrum388.graph sourceMap5215swap=true := by decide +kernel
theorem fusedMap5215swap_checked : acceptsGraphIso
    (fused (graph core5215) (root 2) 5 2) DegreeOneSmallSpectrum378.graph fusedMap5215swap=true := by decide +kernel
theorem certified5215swap : Certified (graph core5215) (root 2) 5 2 :=
  of_native_maps core5215 DegreeOneSmallSpectrum388.graph DegreeOneSmallSpectrum378.graph
    sourceMap5215swap fusedMap5215swap sourceMap5215swap_checked fusedMap5215swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5215
#print axioms sourceMap5215swap_checked
#print axioms fusedMap5215swap_checked
#print axioms certified5215swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
