/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0485 : Family 10 := level10.get ⟨352,by decide⟩
def sourceMap0485 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,7,6,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0485 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0485_checked : acceptsGraphIso
    (source (graph core0485) (root 10) 0 0) DegreeOneSmallSpectrum1025.graph sourceMap0485=true := by decide +kernel
theorem fusedMap0485_checked : acceptsGraphIso
    (fused (graph core0485) (root 10) 0 0) DegreeOneSmallSpectrum1426.graph fusedMap0485=true := by decide +kernel
theorem certified0485 : Certified (graph core0485) (root 10) 0 0 :=
  of_native_maps core0485 DegreeOneSmallSpectrum1025.graph DegreeOneSmallSpectrum1426.graph
    sourceMap0485 fusedMap0485 sourceMap0485_checked fusedMap0485_checked
    DegreeTwoThreeFiniteComparisons.comparison0485
#print axioms sourceMap0485_checked
#print axioms fusedMap0485_checked
#print axioms certified0485
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
