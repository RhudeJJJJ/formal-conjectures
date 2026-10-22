/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0472 : Family 10 := level10.get ⟨302,by decide⟩
def sourceMap0472 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0472 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0472_checked : acceptsGraphIso
    (source (graph core0472) (root 10) 0 0) DegreeOneSmallSpectrum1335.graph sourceMap0472=true := by decide +kernel
theorem fusedMap0472_checked : acceptsGraphIso
    (fused (graph core0472) (root 10) 0 0) DegreeOneSmallSpectrum1332.graph fusedMap0472=true := by decide +kernel
theorem certified0472 : Certified (graph core0472) (root 10) 0 0 :=
  of_native_maps core0472 DegreeOneSmallSpectrum1335.graph DegreeOneSmallSpectrum1332.graph
    sourceMap0472 fusedMap0472 sourceMap0472_checked fusedMap0472_checked
    DegreeTwoThreeFiniteComparisons.comparison0472
#print axioms sourceMap0472_checked
#print axioms fusedMap0472_checked
#print axioms certified0472
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
