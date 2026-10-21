/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons49
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2483 : Family 10 := level10.get ⟨1709,by decide⟩
def sourceMap2483 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,12,2,3] (sourceLabel 10 0 0 v)
def fusedMap2483 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2483_checked : acceptsGraphIso
    (source (graph core2483) (root 10) 0 0) DegreeOneSmallSpectrum2018.graph sourceMap2483=true := by decide +kernel
theorem fusedMap2483_checked : acceptsGraphIso
    (fused (graph core2483) (root 10) 0 0) DegreeOneSmallSpectrum1898.graph fusedMap2483=true := by decide +kernel
theorem certified2483 : Certified (graph core2483) (root 10) 0 0 :=
  of_native_maps core2483 DegreeOneSmallSpectrum2018.graph DegreeOneSmallSpectrum1898.graph
    sourceMap2483 fusedMap2483 sourceMap2483_checked fusedMap2483_checked
    DegreeOneSmallComparisons.comparison2483
#print axioms sourceMap2483_checked
#print axioms fusedMap2483_checked
#print axioms certified2483
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
