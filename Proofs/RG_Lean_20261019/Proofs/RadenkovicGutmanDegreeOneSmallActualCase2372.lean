/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons47
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2372 : Family 10 := level10.get ⟨1135,by decide⟩
def sourceMap2372 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,4,5,6,2,3] (sourceLabel 10 0 0 v)
def fusedMap2372 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2372_checked : acceptsGraphIso
    (source (graph core2372) (root 10) 0 0) DegreeOneSmallSpectrum1713.graph sourceMap2372=true := by decide +kernel
theorem fusedMap2372_checked : acceptsGraphIso
    (fused (graph core2372) (root 10) 0 0) DegreeOneSmallSpectrum1808.graph fusedMap2372=true := by decide +kernel
theorem certified2372 : Certified (graph core2372) (root 10) 0 0 :=
  of_native_maps core2372 DegreeOneSmallSpectrum1713.graph DegreeOneSmallSpectrum1808.graph
    sourceMap2372 fusedMap2372 sourceMap2372_checked fusedMap2372_checked
    DegreeOneSmallComparisons.comparison2372
#print axioms sourceMap2372_checked
#print axioms fusedMap2372_checked
#print axioms certified2372
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
