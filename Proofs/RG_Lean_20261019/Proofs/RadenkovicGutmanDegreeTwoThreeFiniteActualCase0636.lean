/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0636 : Family 10 := level10.get ⟨796,by decide⟩
def sourceMap0636 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0636 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0636_checked : acceptsGraphIso
    (source (graph core0636) (root 10) 0 0) DegreeOneSmallSpectrum1432.graph sourceMap0636=true := by decide +kernel
theorem fusedMap0636_checked : acceptsGraphIso
    (fused (graph core0636) (root 10) 0 0) DegreeOneSmallSpectrum1430.graph fusedMap0636=true := by decide +kernel
theorem certified0636 : Certified (graph core0636) (root 10) 0 0 :=
  of_native_maps core0636 DegreeOneSmallSpectrum1432.graph DegreeOneSmallSpectrum1430.graph
    sourceMap0636 fusedMap0636 sourceMap0636_checked fusedMap0636_checked
    DegreeTwoThreeFiniteComparisons.comparison0636
#print axioms sourceMap0636_checked
#print axioms fusedMap0636_checked
#print axioms certified0636
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
