/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2433 : Family 10 := level10.get ⟨1348,by decide⟩
def sourceMap2433 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap2433 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,12,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap2433_checked : acceptsGraphIso
    (source (graph core2433) (root 10) 0 0) DegreeOneSmallSpectrum1968.graph sourceMap2433=true := by decide +kernel
theorem fusedMap2433_checked : acceptsGraphIso
    (fused (graph core2433) (root 10) 0 0) DegreeOneSmallSpectrum1964.graph fusedMap2433=true := by decide +kernel
theorem certified2433 : Certified (graph core2433) (root 10) 0 0 :=
  of_native_maps core2433 DegreeOneSmallSpectrum1968.graph DegreeOneSmallSpectrum1964.graph
    sourceMap2433 fusedMap2433 sourceMap2433_checked fusedMap2433_checked
    DegreeOneSmallComparisons.comparison2433
#print axioms sourceMap2433_checked
#print axioms fusedMap2433_checked
#print axioms certified2433
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
